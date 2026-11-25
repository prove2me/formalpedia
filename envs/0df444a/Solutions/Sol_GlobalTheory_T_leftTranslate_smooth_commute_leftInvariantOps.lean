-- Prove2me | solution 1 for GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:31:11.607959+00:00
-- url     : https://prove2.me/submissions/899cd96e-1088-48af-be28-73b2eb4b11e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOps
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOpsStatement
import Theorems.Thm_GlobalTheory_leftTranslate_smooth_commute


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G), ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  first | exact @GlobalTheory.leftTranslate_smooth_commute | exact GlobalTheory.leftTranslate_smooth_commute | (intros; apply GlobalTheory.leftTranslate_smooth_commute <;> assumption)
end _root_.GlobalTheory.T
