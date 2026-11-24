-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:23:25.47715+00:00
-- url     : https://prove2.me/submissions/35dc4e4e-34af-43ae-8552-b728bd290aba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  first | exact @GlobalTheory.UnitLemma.Unr.intO | exact GlobalTheory.UnitLemma.Unr.intO | (intros; apply GlobalTheory.UnitLemma.Unr.intO <;> assumption)
end _root_.GlobalTheory.T
