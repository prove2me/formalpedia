-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.nrm_le_of_val_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:09:33.017631+00:00
-- url     : https://prove2.me/submissions/6ef5e63d-f551-4f6f-9127-8e59063b6279

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_nrm_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution (h : LF O ϖ nrm q) {x y : F}
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : nrm x ≤ nrm y := by
  by_cases hy : y = 0
  · have hv0 : ValuativeRel.valuation F x = 0 := by
      rw [hy, map_zero] at hxy
      exact le_antisymm hxy zero_le
    have hx : x = 0 := (Valuation.zero_iff _).1 hv0
    simp [hx]
  · have hyv : ValuativeRel.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have hq : ValuativeRel.valuation F (x * y⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      calc ValuativeRel.valuation F x * (ValuativeRel.valuation F y)⁻¹
          ≤ ValuativeRel.valuation F y * (ValuativeRel.valuation F y)⁻¹ := by gcongr
        _ = 1 := _root_.mul_inv_cancel₀ hyv
    have h1 := (nrm_le_one_iff h _).2 hq
    rw [map_mul, map_inv₀] at h1
    have hpos : 0 < nrm y := nrm.pos hy
    calc nrm x = nrm x * (nrm y)⁻¹ * nrm y := (_root_.inv_mul_cancel_right₀ hpos.ne' _).symm
      _ ≤ 1 * nrm y := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = nrm y := one_mul _
end GlobalTheory.CompanionTheory.QL.NormalisedValue
