-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.NormValU.val_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:54.208706+00:00
-- url     : https://prove2.me/submissions/da9a9061-6908-4d99-9e75-3f902700567c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormValU_val_mul_ne
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormValU_val_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormValU
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]
namespace GlobalTheory.UnitLemma.Unr.NormValU
theorem _root_.solution {x : E} (hx : x ≠ 0) : val O x⁻¹ = -val O x := by
  have := val_mul_ne O hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, val_one_eq] at this
  omega
end GlobalTheory.UnitLemma.Unr.NormValU
