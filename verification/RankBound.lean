module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! # Endpoint bounds from vanishing moments

Test against a product of linear factors to isolate the distinguished end (index 0).
For rational nodes, a chain of valuations gives a triangular prime-power divisor.
For real nodes whose absolute values halve, the same product and one extra factor
of `T` give an archimedean bound using only strictly positive moments.
-/

public section

namespace RankBound

/-- Vanishing power moments annihilate any monic product of the corresponding degree. -/
theorem annihilate {K : Type*} [CommRing K] (n : ℕ) (w t : ℕ → K) (roots : List K)
    (hm : ∀ j ≤ roots.length, ∑ i ∈ Finset.range (n+1), w i * (t i)^j = 0) :
    ∑ i ∈ Finset.range (n+1), w i * (roots.map (fun r => t i-r)).prod = 0 := by
  induction roots generalizing w with
  | nil => simpa using hm 0 (by simp)
  | cons r roots ih =>
    simp only [List.map_cons, List.prod_cons, ← mul_assoc]
    apply ih
    intro j hj
    calc
      _ = ∑ i ∈ Finset.range (n+1), (w i * (t i)^(j+1) - r * (w i * (t i)^j)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hm (j+1) (by simpa using hj),
          hm j (by simp; omega)]
        simp

-- The annihilator kills nodes 1,...,r; node 0 is the distinguished endpoint.
private def roots {K : Type*} (t : ℕ → K) (r : ℕ) := (List.range r).map fun j => t (j+1)
private def evalRoots {K : Type*} [CommRing K] (t : ℕ → K) (r i : ℕ) : K :=
  ((roots t r).map (fun z => t i - z)).prod

private lemma eval_succ {K : Type*} [CommRing K] (t : ℕ → K) (r i : ℕ) :
    evalRoots t (r+1) i = evalRoots t r i * (t i - t (r+1)) := by
  simp [evalRoots, roots, List.range_succ]

private lemma eval_root {K : Type*} [CommRing K] (t : ℕ → K) {r i : ℕ} (hi : 0 < i) (hir : i ≤ r) :
    evalRoots t r i = 0 := by
  induction r with
  | zero => omega
  | succ r ih =>
    rw [eval_succ]
    by_cases eq : i = r+1
    · simp [eq]
    · rw [ih (by omega), zero_mul]

variable {p n : ℕ} [Fact p.Prime] {t : ℕ → ℚ}

private theorem val_sub {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : padicValRat p a < padicValRat p b) :
    a - b ≠ 0 ∧ padicValRat p (a-b) = padicValRat p a := by
  have ne : a - b ≠ 0 := sub_ne_zero.mpr (fun he => by simp [he] at h)
  refine ⟨ne, ?_⟩
  rw [sub_eq_add_neg] at ne ⊢
  exact padicValRat.add_eq_of_lt ne ha (neg_ne_zero.mpr hb) (by simpa using h)

omit [Fact p.Prime] in
private theorem gap_of_inc
    (inc : ∀ j < n, padicValRat p (t j) < padicValRat p (t (j+1))) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    padicValRat p (t i) + (j : ℤ) - i ≤ padicValRat p (t j) := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp
  | succ j ih =>
    by_cases eq : i = j+1
    · subst i; omega
    · have := ih (by omega) (by omega); have := inc j (by omega); omega

private theorem eval_zero_ne (nz : ∀ i ≤ n, t i ≠ 0)
    (inc : ∀ j < n, padicValRat p (t j) < padicValRat p (t (j+1)))
    {r : ℕ} (hr : r ≤ n) : evalRoots t r 0 ≠ 0 := by
  induction r with
  | zero => simp [evalRoots, roots]
  | succ r ih =>
    rw [eval_succ]
    have hg := gap_of_inc inc (i:=0) (j:=r+1) (by omega) hr
    exact mul_ne_zero (ih (by omega)) (val_sub (nz 0 (by omega)) (nz _ hr) (p:=p) (by omega)).1

/-- At a surviving nonterminal node the valuation advantage of the annihilator
is at least 1+2+...+r. Each factor contributes the corresponding valuation gap. -/
private theorem eval_gap (nz : ∀ i ≤ n, t i ≠ 0)
    (inc : ∀ j < n, padicValRat p (t j) < padicValRat p (t (j+1)))
    {r i : ℕ} (hr : r < i) (hi : i ≤ n) :
    evalRoots t r i ≠ 0 ∧
      padicValRat p (evalRoots t r 0) + ((r+1).choose 2 : ℕ) ≤ padicValRat p (evalRoots t r i) := by
  induction r with
  | zero => simp [evalRoots, roots]
  | succ r ih =>
    obtain ⟨prev, H⟩ := ih (by omega)
    have g := gap_of_inc inc (i:=0) (j:=r+1) (by omega) (by omega)
    have g' := gap_of_inc inc (i:=r+1) (j:=i) (by omega) hi
    obtain ⟨ne0, v0⟩ := val_sub (p:=p) (nz 0 (by omega)) (nz (r+1) (by omega)) (by omega)
    obtain ⟨ne', v'⟩ := val_sub (p:=p) (nz (r+1) (by omega)) (nz i hi) (by omega)
    have ne : t i - t (r+1) ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp ne').symm
    have v : padicValRat p (t i - t (r+1)) = padicValRat p (t (r+1)) := by
      rw [← neg_sub (t (r+1)) (t i), padicValRat.neg, v']
    simp only [eval_succ, padicValRat.mul prev ne,
      padicValRat.mul (eval_zero_ne nz inc (by omega : r ≤ n)) ne0, v0, v]
    refine ⟨mul_ne_zero prev ne, ?_⟩
    rw [show (r+1+1).choose 2 = (r+1) + (r+1).choose 2 by
      rw [Nat.choose_succ_succ (r+1) 1, Nat.choose_one_right]]
    omega

private lemma val_sum {f : ℕ → ℚ} {b : ℤ} {m : ℕ}
    (hb : ∀ i < m, f i ≠ 0 → b ≤ padicValRat p (f i)) (hn : ∑ i ∈ Finset.range m, f i ≠ 0) :
    b ≤ padicValRat p (∑ i ∈ Finset.range m, f i) := by
  induction m with
  | zero => simp at hn
  | succ m ih =>
    rw [Finset.sum_range_succ] at hn ⊢
    by_cases h0 : ∑ i ∈ Finset.range m, f i = 0
    · simpa [h0] using hb m (by omega) (by simpa [h0] using hn)
    by_cases h1 : f m = 0
    · simpa [h1] using ih (fun i hi => hb i (by omega)) h0
    exact le_trans (le_min (ih (fun i hi => hb i (by omega)) h0) (hb m (by omega) h1))
      (padicValRat.min_le_padicValRat_add hn)

/-- Number nodes from the distinguished end: valuations strictly increase away from node 0.
Vanishing through degree `d` forces a triangular prime-power divisor of the end weight.
No restrictions are imposed on the remaining integer weights, including their signs or zeros. -/
theorem primePower_dvd_endWeight (p n d : ℕ) [Fact p.Prime] (t : ℕ → ℚ) (w : ℕ → ℤ)
    (nz : ∀ i ≤ n, t i ≠ 0)
    (inc : ∀ j < n, padicValRat p (t j) < padicValRat p (t (j+1)))
    (hm : ∀ j ≤ d, ∑ i ∈ Finset.range (n+1), (w i : ℚ) * (t i)^j = 0) :
    (p : ℤ) ^ (d+1).choose 2 ∣ w 0 := by
  by_cases hw : w 0 = 0
  · simp [hw]
  let r := min d n
  let f (i : ℕ) : ℚ := (w i : ℚ) * evalRoots t r i
  have hr : r ≤ n := Nat.min_le_right ..
  have van : ∑ i ∈ Finset.range (n+1), f i = 0 := by
    apply annihilate n (fun i => (w i : ℚ)) t (roots t r)
    intro j hj
    exact hm j (le_trans (by simpa [roots] using hj : j ≤ r) (Nat.min_le_left ..))
  rw [Finset.sum_range_succ'] at van
  have vsum : ∑ i ∈ Finset.range n, f (i+1) = -f 0 := (neg_eq_of_add_eq_zero_left van).symm
  have hF := eval_zero_ne nz inc hr
  have hwQ : (w 0 : ℚ) ≠ 0 := by exact_mod_cast hw
  have hf0 : f 0 ≠ 0 := mul_ne_zero hwQ hF
  have bound : padicValRat p (evalRoots t r 0) + ((d+1).choose 2 : ℕ) ≤
      padicValRat p (∑ i ∈ Finset.range n, f (i+1)) := by
    apply val_sum (p:=p) _ (by rw [vsum]; exact neg_ne_zero.mpr hf0)
    intro i hi hn
    obtain ⟨hw', he⟩ := mul_ne_zero_iff.mp hn
    have hir : r < i+1 := by
      by_contra! le
      exact he (eval_root t (by omega) le)
    have rd : r = d := by dsimp [r] at hir ⊢; omega
    obtain ⟨_, gap⟩ := eval_gap nz inc hir (by omega : i+1 ≤ n)
    change _ ≤ padicValRat p ((w (i+1) : ℚ) * _)
    rw [padicValRat.mul hw' he, padicValRat.of_int, ← rd]
    omega
  rw [vsum, padicValRat.neg] at bound
  change _ ≤ padicValRat p ((w 0 : ℚ) * evalRoots t r 0) at bound
  rw [padicValRat.mul hwQ hF, padicValRat.of_int] at bound
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))

/-- For a bounded nonzero end weight, some moment of degree at most `d` survives. -/
theorem exists_ne_zero_moment (p n d : ℕ) [Fact p.Prime] (t : ℕ → ℚ) (w : ℕ → ℤ)
    (nz : ∀ i ≤ n, t i ≠ 0)
    (inc : ∀ j < n, padicValRat p (t j) < padicValRat p (t (j+1)))
    (hw : w 0 ≠ 0) (small : (w 0).natAbs < p ^ (d+1).choose 2) :
    ∃ j ≤ d, ∑ i ∈ Finset.range (n+1), (w i : ℚ) * (t i)^j ≠ 0 := by
  by_contra! all_zero
  have h := Int.natAbs_dvd_natAbs.mpr (primePower_dvd_endWeight p n d t w nz inc all_zero)
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h
  exact (Nat.not_le_of_lt small) (Nat.le_of_dvd (Int.natAbs_pos.mpr hw) h)

/-! ## The real moment bound for geometrically separated backward gaps -/

private theorem lacunary_le {n : ℕ} {a : ℕ → ℝ}
    (sep : ∀ j < n, 2 * |a (j+1)| ≤ |a j|) {j i : ℕ} (hji : j < i) (hi : i ≤ n) :
    2 * |a i| ≤ |a j| := by
  induction i with
  | zero => omega
  | succ i ih =>
    have h := sep i (by omega)
    by_cases eq : j=i
    · simpa [eq] using h
    · have := ih (by omega) (by omega); linarith [abs_nonneg (a (i+1))]

private theorem lacunary_pow {n : ℕ} {a : ℕ → ℝ}
    (sep : ∀ j < n, 2 * |a (j+1)| ≤ |a j|) {j : ℕ} (hj : j+1 ≤ n) :
    (2:ℝ)^(j+1) * |a (j+1)| ≤ |a 0| := by
  induction j with
  | zero => simpa using sep 0 (by omega)
  | succ j ih =>
    have h := ih (by omega)
    have h' := sep (j+1) (by omega)
    rw [pow_succ, mul_assoc]
    exact le_trans (mul_le_mul_of_nonneg_left h' (by positivity)) h

private theorem real_eval_gap {n : ℕ} {a : ℕ → ℝ}
    (sep : ∀ j < n, 2 * |a (j+1)| ≤ |a j|) {r i : ℕ} (hr : r < i) (hi : i ≤ n) :
    (2:ℝ)^((r+1).choose 2) * |evalRoots a r i| ≤ 3^r * |evalRoots a r 0| := by
  induction r with
  | zero => simp [evalRoots, roots]
  | succ r ih =>
    have prev := ih (by omega)
    let j := r+1
    have grow := lacunary_pow sep (j:=r) (by omega)
    have ratio := lacunary_le sep (j:=j) (i:=i) hr hi
    have first := lacunary_le sep (j:=0) (i:=j) (by dsimp [j]; omega) (by omega)
    have upper : |a i - a j| ≤ (3/2:ℝ) * |a j| := by linarith [abs_sub (a i) (a j), abs_nonneg (a i)]
    have low : |a 0|/2 ≤ |a 0 - a j| := by linarith [abs_sub_abs_le_abs_sub (a 0) (a j)]
    have factor : (2:ℝ)^j * |a i - a j| ≤ 3 * |a 0 - a j| := by
      calc
        _ ≤ 2^j * ((3/2) * |a j|) := mul_le_mul_of_nonneg_left upper (by positivity)
        _ = (3/2)*(2^j*|a j|) := by ring
        _ ≤ (3/2)*|a 0| := mul_le_mul_of_nonneg_left grow (by norm_num)
        _ ≤ _ := by linarith
    rw [Nat.choose_succ_succ (r+1) 1, Nat.choose_one_right, pow_add]
    simp only [eval_succ, abs_mul, pow_succ (3:ℝ)]
    convert mul_le_mul prev factor (by positivity) (by positivity) using 1 <;> dsimp [j] <;> ring

-- The factor T in the test polynomial pays for the whole tail, not just one term.
private theorem lacunary_tail {n : ℕ} {a : ℕ → ℝ}
    (sep : ∀ j < n, 2 * |a (j+1)| ≤ |a j|) :
    (∑ i ∈ Finset.range n, |a (i+1)|) + |a n| ≤ |a 0| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have H := ih (fun i hi => sep i (by omega))
    rw [Finset.sum_range_succ]
    linarith [sep n (by omega), abs_nonneg (a (n+1))]

/-- A signed real lacunary family cannot kill many successive *positive* moments with small
weights. Neither the number of nodes nor a bound on the distinguished weight occurs on the
right. Only the initial node must be nonzero; signs of all nodes and weights are arbitrary. -/
theorem lacunary_endWeight (n d : ℕ) (a w : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (nz : a 0 ≠ 0) (sep : ∀ j < n, 2 * |a (j+1)| ≤ |a j|)
    (bounded : ∀ i < n, |w (i+1)| ≤ M)
    (hm : ∀ j ≤ d, ∑ i ∈ Finset.range (n+1), w i * (a i)^(j+1) = 0) :
    (2:ℝ)^((d+1).choose 2) * |w 0| ≤ 3^d * M := by
  let r := min d n
  let f (i : ℕ) : ℝ := (w i * a i) * evalRoots a r i
  let P : ℝ := 2^((d+1).choose 2)
  have vanish : ∑ i ∈ Finset.range (n+1), f i = 0 := by
    apply annihilate n (fun i => w i * a i) a (roots a r)
    intro j hj
    simpa only [pow_succ', ← mul_assoc] using hm j (le_trans (by simpa [roots] using hj : j ≤ r) (Nat.min_le_left ..))
  rw [Finset.sum_range_succ'] at vanish
  have at0 := (neg_eq_of_add_eq_zero_left vanish).symm
  have hF : ∀ k ≤ n, evalRoots a k 0 ≠ 0 := by
    intro k hk
    induction k with
    | zero => simp [evalRoots, roots]
    | succ k ih =>
      rw [eval_succ]
      refine mul_ne_zero (ih (by omega)) (sub_ne_zero.mpr ?_)
      intro eq
      have h := lacunary_le sep (j:=0) (i:=k+1) (by omega) hk
      rw [← eq] at h
      linarith [abs_pos.mpr nz]
  let B : ℝ := 3^d * M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have each (i : ℕ) (hi : i < n) : P * |f (i+1)| ≤ (B * |evalRoots a r 0|) * |a (i+1)| := by
    by_cases le : i+1 ≤ r
    · simp only [f, eval_root a (by omega : 0 < i+1) le, mul_zero, abs_zero]
      positivity
    have rd : r = d := by dsimp [r] at le ⊢; omega
    have gap := real_eval_gap sep (r:=r) (i:=i+1) (by omega) (by omega)
    have gap' : P * |evalRoots a r (i+1)| ≤ 3^d * |evalRoots a r 0| := by simpa only [P, ← rd] using gap
    calc
      _ = (|w (i+1)| * (P * |evalRoots a r (i+1)|)) * |a (i+1)| := by simp only [f, abs_mul]; ring
      _ ≤ (M * (3^d * |evalRoots a r 0|)) * |a (i+1)| := mul_le_mul_of_nonneg_right (mul_le_mul (bounded i hi) gap' (by dsimp [P]; positivity) hM) (abs_nonneg _)
      _ = _ := by dsimp [B]; ring
  have htail := lacunary_tail sep
  have sum_le : (∑ i ∈ Finset.range n, |a (i+1)|) ≤ |a 0| := by linarith [abs_nonneg (a n)]
  have total : P * |f 0| ≤ B * |evalRoots a r 0| * |a 0| := calc
    _ = P * |∑ i ∈ Finset.range n, f (i+1)| := by rw [at0, abs_neg]
    _ ≤ P * ∑ i ∈ Finset.range n, |f (i+1)| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (by dsimp [P]; positivity)
    _ = ∑ i ∈ Finset.range n, P * |f (i+1)| := Finset.mul_sum ..
    _ ≤ ∑ i ∈ Finset.range n, (B * |evalRoots a r 0|) * |a (i+1)| := Finset.sum_le_sum (fun i hi => each i (Finset.mem_range.mp hi))
    _ = (B * |evalRoots a r 0|) * ∑ i ∈ Finset.range n, |a (i+1)| := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left sum_le (mul_nonneg hB (abs_nonneg _))
  have pos := mul_pos (abs_pos.mpr (hF r (Nat.min_le_right ..))) (abs_pos.mpr nz)
  apply (mul_le_mul_iff_left₀ pos).mp
  calc
    _ = P * |f 0| := by simp only [f, abs_mul, P]; ring
    _ ≤ B * |evalRoots a r 0| * |a 0| := total
    _ = _ := mul_assoc ..

end RankBound

#print axioms RankBound.primePower_dvd_endWeight
#print axioms RankBound.exists_ne_zero_moment
#print axioms RankBound.lacunary_endWeight
