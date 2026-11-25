-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:14:37.792863+00:00
-- url     : https://prove2.me/submissions/d04587cb-2a6b-467f-b813-b1a6502960c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroOfOrthogonalSchrodingerGaussian
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqZeroOfOrthogonalSchrodingerGaussianStatement
import Theorems.Thm_GlobalTheory_RealWeil_eq_zero_of_inner_rhoSch_gaussian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : Type) [Fintype l] (k : Sch l), (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume) (k.toLp 2 volume) = 0) → k = 0 := by
  first | exact @GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | exact GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | (intros; apply GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian <;> assumption)
end _root_.GlobalTheory.T
