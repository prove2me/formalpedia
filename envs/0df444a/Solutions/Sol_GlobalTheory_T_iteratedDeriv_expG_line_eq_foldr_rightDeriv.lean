-- Prove2me | solution 1 for GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:34.583794+00:00
-- url     : https://prove2.me/submissions/91e623db-361d-4395-8445-7eae311c3dc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPow
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Theorems.Thm_GlobalTheory_iteratedDeriv_expG_line_eq_rightDeriv_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
  first | exact @GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow | exact GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow | (intros; apply GlobalTheory.iteratedDeriv_expG_line_eq_rightDeriv_pow <;> assumption)
end _root_.GlobalTheory.T
