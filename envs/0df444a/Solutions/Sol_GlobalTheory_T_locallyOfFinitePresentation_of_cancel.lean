-- Prove2me | solution 1 for GlobalTheory.T.locallyOfFinitePresentation_of_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:37.320689+00:00
-- url     : https://prove2.me/submissions/5af4fd34-8ca9-43dc-89c4-c2185e71b651

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_LocallyOfFinitePresentationOfCancel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_LocallyOfFinitePresentationOfCancelStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LfpDescent_descends
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q → LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) → LocallyOfFinitePresentation f := by
  first | exact @GlobalTheory.CompanionTheory.LfpDescent.descends | exact GlobalTheory.CompanionTheory.LfpDescent.descends | (intros; apply GlobalTheory.CompanionTheory.LfpDescent.descends <;> assumption)
end _root_.GlobalTheory.T
