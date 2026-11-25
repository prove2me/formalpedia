-- Prove2me | solution 1 for GlobalTheory.T.rightDerivWord_expCoords_differentialOperator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:33:00.692846+00:00
-- url     : https://prove2.me/submissions/a9388579-7ce5-4af4-a986-5a8ffa9444e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightDerivWordExpCoordsDifferentialOperator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightDerivWordExpCoordsDifferentialOperatorStatement
import Theorems.Thm_GlobalTheory_WordExp_word_apOp


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
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ l : List 𝔤, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ x ∈ Metric.ball (0 : E d) r, l.foldr h.rightDeriv f (h.expG (coordEquiv b (x))) = apOp l.length a (fun y => f (h.expG (coordEquiv b (y)))) x := by
  first | exact @GlobalTheory.WordExp.word_apOp | exact GlobalTheory.WordExp.word_apOp | (intros; apply GlobalTheory.WordExp.word_apOp <;> assumption)
end _root_.GlobalTheory.T
