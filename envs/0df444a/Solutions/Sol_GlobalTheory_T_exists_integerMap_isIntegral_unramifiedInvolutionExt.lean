-- Prove2me | solution 1 for GlobalTheory.T.exists_integerMap_isIntegral_unramifiedInvolutionExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:47.536158+00:00
-- url     : https://prove2.me/submissions/7cd4ddcd-afe8-4751-a2ca-fff411ed63cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionEx
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intMap_isIntegral_of_unr


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
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧ @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := by
  first | exact @GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | exact GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr | (intros; apply GlobalTheory.UnitLemma.Unr.intMap_isIntegral_of_unr <;> assumption)
end _root_.GlobalTheory.T
