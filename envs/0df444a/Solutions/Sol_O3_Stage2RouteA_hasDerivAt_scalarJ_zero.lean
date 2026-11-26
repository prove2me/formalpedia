-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_scalarJ_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:34.239091+00:00
-- url     : https://prove2.me/submissions/0b9a53c3-6991-47e8-95b2-dd4f73a81238

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {q : ℝ} (hq : 2 < q) :
    HasDerivAt (O3.Experimental.scalarJ q) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hcont : Filter.Tendsto (fun t : ℝ ↦ |t| ^ (q - 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    change Filter.Tendsto (fun t : ℝ ↦ |t| ^ (q - 2))
      (nhds 0 ⊓ Filter.principal {0}ᶜ) (nhds 0)
    have hc : ContinuousAt (fun t : ℝ ↦ |t| ^ (q - 2)) 0 :=
      (continuous_abs.continuousAt.rpow_const
        (Or.inr (by linarith : 0 ≤ q - 2)))
    simpa [Real.zero_rpow (by linarith : q - 2 ≠ 0)] using
      hc.tendsto.mono_left inf_le_left
  apply hcont.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  simp only [zero_add, O3.Experimental.scalarJ, abs_zero, smul_eq_mul]
  rw [Real.zero_rpow (by linarith : q - 2 ≠ 0), zero_mul, sub_zero]
  field_simp
end O3.Stage2RouteA
