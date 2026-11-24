-- Prove2me | solution 1 for GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:34.416349+00:00
-- url     : https://prove2.me/submissions/5088b3e5-b2c0-4fd7-a91e-84048942244e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormValU_val_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormValU.val_norm | exact GlobalTheory.UnitLemma.Unr.NormValU.val_norm | (intros; apply GlobalTheory.UnitLemma.Unr.NormValU.val_norm <;> assumption)
end _root_.GlobalTheory.T
