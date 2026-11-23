-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.NormValU.val_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:01.940834+00:00
-- url     : https://prove2.me/submissions/39a3b69b-d7d9-4e55-ace4-6201f367fd23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExt

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
theorem _root_.solution : val O (1 : E) = 0 := by simp [val]
end GlobalTheory.UnitLemma.Unr.NormValU
