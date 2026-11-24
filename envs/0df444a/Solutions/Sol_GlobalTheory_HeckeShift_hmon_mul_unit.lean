-- Prove2me | solution 1 for GlobalTheory.HeckeShift.hmon_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:44.865571+00:00
-- url     : https://prove2.me/submissions/fe39a3c5-9618-40d7-9651-c884ff2830a9

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeShift
namespace GlobalTheory.HeckeShift
theorem _root_.solution {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℤ) (v : ℂ) :
    GlobalTheory.HeckeTheta.hmon n (ζ * v) = ζ ^ (-n) * GlobalTheory.HeckeTheta.hmon n v := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · have hc : starRingEnd ℂ ζ = ζ⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul, mul_pow, hc, inv_pow, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg h]
  · rw [mul_pow, ← zpow_natCast ζ, Int.toNat_of_nonneg (by omega)]
end GlobalTheory.HeckeShift
