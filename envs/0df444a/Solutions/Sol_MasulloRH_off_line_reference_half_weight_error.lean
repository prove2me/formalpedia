-- Prove2me | solution 1 for MasulloRH.off_line_reference_half_weight_error
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:54:52.75986+00:00
-- url     : https://prove2.me/submissions/70507a7a-57c6-41bc-9c6c-0cf573fc1499

import Theorems.Thm_MasulloRH_reference_real_resolvent_half_weight_error
import Theorems.Thm_MasulloRH_reference_real_resolvent_sandwich
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_certified_height_99998_reference_budget
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

theorem solution :
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2}
    let W := ∑' z : Z, zeroDecayWeight (1/2) z.val
    let K := ∑' z : Z, (zeroResolventTerm (1/2) 3 z.val).re
    0 ≤ W/2-K ∧ (1+99998^2)*(W/2-K) ≤ 16*W := by
  classical
  let A : Set (ZetaZerosInTraceStrip (1/2)) := {z | z.val.re ≠ 1/2}
  let w (z : A) := zeroDecayWeight (1/2) z.val
  let k (z : A) := (zeroResolventTerm (1/2) 3 z.val).re
  let e (z : A) := (1/2:ℝ)*w z-k z
  let C : ℝ := 1+99998^2
  have hw : Summable w := (weighted_zero_summability (1/2) (by norm_num)).subtype A
  have hk : Summable k := by
    apply hw.of_norm_bounded
    intro z
    have h := reference_real_resolvent_sandwich z.val
    have hnn : 0 ≤ w z := by dsimp [w,zeroDecayWeight]; positivity
    change w z/4 ≤ k z ∧ k z ≤ w z/2 at h
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith only [h.1,h.2,hnn]
  have he : Summable e := (hw.mul_left (1/2:ℝ)).sub hk
  have h0 (z : A) : 0 ≤ e z := by
    have h := (reference_real_resolvent_half_weight_error z.val).1
    change 0 ≤ w z/2-k z at h
    dsimp [e]; linarith
  have hpt (z : A) : C*e z ≤ 16*w z := by
    have hcov := certified_height_99998_reference_budget.1
    have ht : (99998:ℝ) ≤ |z.val.val.im| := by
      by_contra! h
      exact z.property (hcov z.val (h.le.trans (by norm_num)))
    have hsq := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 99998) ht
    have hc : C ≤ 1+z.val.val.im^2 := by
      dsimp [C]; nlinarith only [hsq,sq_abs z.val.val.im]
    apply (mul_le_mul_of_nonneg_right hc (h0 z)).trans
    simpa only [e,w,k,div_eq_inv_mul,mul_one] using (reference_real_resolvent_half_weight_error z.val).2
  have hs := (he.mul_left C).tsum_le_tsum hpt (hw.mul_left 16)
  rw [tsum_mul_left,tsum_mul_left] at hs
  have hid : (∑' z,e z) = (∑' z,w z)/2 - ∑' z,k z := by
    change (∑' z,((1/2:ℝ)*w z-k z)) = _
    rw [((hw.mul_left (1/2:ℝ)).tsum_sub hk),tsum_mul_left]; ring
  change 0 ≤ (∑' z,w z)/2 - ∑' z,k z ∧ C*((∑' z,w z)/2 - ∑' z,k z) ≤ 16*∑' z,w z
  rw [←hid]
  exact ⟨tsum_nonneg h0,hs⟩
