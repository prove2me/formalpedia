-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.NormValU.val_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:40.488804+00:00
-- url     : https://prove2.me/submissions/138d6a22-5960-4e52-b037-3e3c6b55daf2

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
theorem _root_.solution {x : E} (hx : x ≠ 0) (k : ℕ) : val O (x ^ k) = k * val O x := by
  induction k with
  | zero => simp [val_one_eq]
  | succ k ih =>
    rw [pow_succ, val_mul_ne O (pow_ne_zero _ hx) hx, ih]
    push_cast; ring
end GlobalTheory.UnitLemma.Unr.NormValU
