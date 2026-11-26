-- Prove2me | solution 1 for MasulloRH.computed_gaussian_upper_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T10:37:01.782802+00:00
-- url     : https://prove2.me/submissions/ed994430-fead-44ff-b31a-2519cd7b48a5

import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.DyadicExp MasulloRH.ComputedGrid MasulloRH.HeightTwoScalar
open scoped BigOperators

private theorem down_mono' {x y : ℚ} (h : x ≤ y) : down x ≤ down y := by
  apply div_le_div_of_nonneg_right _ (by norm_num [scale])
  exact_mod_cast Int.floor_le_floor (mul_le_mul_of_nonneg_right h (by norm_num [scale] : 0 ≤ scale))

private theorem up_mono' {x y : ℚ} (h : x ≤ y) : up x ≤ up y := by
  apply div_le_div_of_nonneg_right _ (by norm_num [scale])
  exact_mod_cast Int.ceil_le_ceil (mul_le_mul_of_nonneg_right h (by norm_num [scale] : 0 ≤ scale))

private theorem base_bounds (t : ℚ) :
    let p := max 1 ⌈4*|t|⌉₊
    let x := |t|/(p:ℚ)
    let a := max (1/2) (down (taylorRat x 9-remainderRat x 9))
    let b := up (taylorRat x 9+remainderRat x 9)
    1 ≤ a ∧ 1 ≤ b ∧ b ≤ 3/2 ∧
      (1/65536 ≤ x → 1+1/131072 ≤ a) := by
  intro p x a b
  have hp : 0 < p := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hp' : (0:ℚ) < p := by exact_mod_cast hp
  have hx0 : 0 ≤ x := div_nonneg (abs_nonneg _) hp'.le
  have hceil : 4*|t| ≤ (p:ℚ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈4*|t|⌉₊))
  have hx : x ≤ 1/4 := (div_le_iff₀ hp').2 (by linarith)
  have h9 : x^9 ≤ x := calc
    x^9 = x^8*x := by ring
    _ ≤ 1*x := mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 (by linarith)) hx0
    _ = x := one_mul _
  have hT : 1+x ≤ taylorRat x 9 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j:ℕ => x^j/(j.factorial:ℚ))
      (Finset.range_mono (show 2 ≤ 9 by decide)) (fun i _ _ => div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
    calc 1+x = taylorRat x 2 := by norm_num [taylorRat, Finset.sum_range_succ]
         _ ≤ _ := h
  have hT' : taylorRat x 9 ≤ taylorRat (1/4) 9 := by
    apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hx _) (Nat.cast_nonneg _)
  have hR : 0 ≤ remainderRat x 9 := by unfold remainderRat; positivity
  have hRx : remainderRat x 9 ≤ x := by
    norm_num [remainderRat,Nat.factorial]
    linarith
  have hRsmall : remainderRat x 9 ≤ 1/262144 := by
    have h : x^9 ≤ 1 := pow_le_one₀ hx0 (by linarith)
    norm_num [remainderRat,Nat.factorial]
    linarith
  have ha : 1 ≤ a := calc
    1 = down 1 := by decide +kernel
    _ ≤ down (taylorRat x 9-remainderRat x 9) := down_mono' (by linarith)
    _ ≤ a := le_max_right _ _
  have hB : 1 ≤ b := calc
    1 = up 1 := by decide +kernel
    _ ≤ b := up_mono' (by linarith)
  have hb : b ≤ 3/2 := calc
    b ≤ up (3/2) := up_mono' ((add_le_add hT' hRsmall).trans (by decide +kernel))
    _ = 3/2 := by decide +kernel
  refine ⟨ha,hB,hb,?_⟩
  intro hmin
  calc 1+1/131072 = down (1+1/131072) := by decide +kernel
       _ ≤ down (taylorRat x 9-remainderRat x 9) := down_mono' (by linarith)
       _ ≤ a := le_max_right _ _

private theorem inner_positive (t : ℚ) (ht : -2 ≤ t) : 1/32 ≤ (row t).lower := by
  by_cases h0 : t=0
  · subst t; norm_num [row]
  have hn : ¬ t ≤ -64 := by linarith
  let p := max 1 ⌈4*|t|⌉₊
  let x := |t|/(p:ℚ)
  let a := max (1/2) (down (taylorRat x 9-remainderRat x 9))
  let b := up (taylorRat x 9+remainderRat x 9)
  obtain ⟨ha,hb,hb',_⟩ := base_bounds t
  change 1 ≤ a at ha
  change 1 ≤ b at hb
  change b ≤ 3/2 at hb'
  by_cases hpos : 0<t
  · simp only [row,if_neg h0,if_neg hn,if_pos hpos]
    change 1/32 ≤ down (a^p)
    calc (1/32:ℚ) ≤ down 1 := by decide +kernel
         _ ≤ _ := down_mono' (one_le_pow₀ ha)
  · have hp8 : p ≤ 8 := max_le (by decide) (Nat.ceil_le.mpr (by
      rw [abs_of_nonpos (le_of_not_gt hpos)]; norm_num; linarith))
    have hpower : b^p ≤ 32 := calc
      b^p ≤ (3/2:ℚ)^p := pow_le_pow_left₀ (by linarith) hb' _
      _ ≤ (3/2:ℚ)^8 := pow_le_pow_right₀ (by norm_num) hp8
      _ ≤ 32 := by norm_num
    simp only [row,if_neg h0,if_neg hn,if_neg hpos]
    change 1/32 ≤ down (1/b^p)
    calc 1/32 = down (1/32) := by decide +kernel
         _ ≤ _ := down_mono' (one_div_le_one_div_of_le (pow_pos (by linarith : 0<b) _) hpower)

private theorem outer_below_one (t : ℚ) (ht : t ≤ -1/256) : (row t).upper < 1 := by
  have h0 : t ≠ 0 := by linarith
  by_cases hn : t ≤ -64
  · norm_num [row,h0,hn]
  have hpos : ¬ 0<t := by linarith
  let p := max 1 ⌈4*|t|⌉₊
  let x := |t|/(p:ℚ)
  let a := max (1/2) (down (taylorRat x 9-remainderRat x 9))
  have hp : 1 ≤ p := le_max_left _ _
  have hp' : (0:ℚ) < p := by exact_mod_cast (Nat.zero_lt_one.trans_le hp)
  have H : p ≤ 256 := max_le (by decide) (Nat.ceil_le.mpr (by
    rw [abs_of_nonpos (le_of_not_gt hpos)]; norm_num; linarith))
  have H' : (p:ℚ) ≤ 256 := by exact_mod_cast H
  have hx : 1/65536 ≤ x := (le_div_iff₀ hp').2 (by
    rw [abs_of_nonpos (le_of_not_gt hpos)]; linarith)
  have ha : 1+1/131072 ≤ a := (base_bounds t).2.2.2 hx
  have hpower : a ≤ a^p := by
    simpa using (pow_le_pow_right₀ (by linarith : 1≤a) hp)
  simp only [row,if_neg h0,if_neg hn,if_neg hpos]
  change up (1/a^p)<1
  exact (up_mono' (one_div_le_one_div_of_le (by norm_num : (0:ℚ)<1+1/131072) (ha.trans hpower))).trans_lt (by decide +kernel)

private theorem GaussianBelow (l u : ℚ) (b : Bool)
    (h : -2 ≤ (if b then -2*u else 2*l)) : (gaussianHi l u b).upper < 1 := by
  have hlow : 1/32 ≤ (innerLo l u b).lower := inner_positive _ h
  have hdiv : 0 < divisor b ∧ divisor b ≤ 16 := by cases b <;> norm_num [divisor]
  apply outer_below_one
  apply (div_le_iff₀ hdiv.1).2
  norm_num [piLowerQ]
  linarith [hdiv.2]

theorem solution (k : ℤ) :
    (gaussianHi (edge k) (edge (k+1)) (decide (k < 24576))).upper < 1 := by
  apply GaussianBelow
  by_cases hk : k < 24576
  · have h : (k:ℚ)+1 ≤ 24576 := by exact_mod_cast (show k+1 ≤ 24576 by omega)
    simp [hk,edge]
    linarith
  · have h : 24576 ≤ (k:ℚ) := by exact_mod_cast (show 24576 ≤ k by omega)
    simp [hk,edge]
    linarith
