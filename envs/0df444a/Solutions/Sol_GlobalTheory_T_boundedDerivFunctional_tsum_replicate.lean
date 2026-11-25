-- Prove2me | solution 1 for GlobalTheory.T.boundedDerivFunctional_tsum_replicate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:58.196958+00:00
-- url     : https://prove2.me/submissions/b5261e81-5d21-41ad-9537-37c179935f12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalTsumReplicate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalTsumReplicateStatement
import Theorems.Thm_GlobalTheory_HCA_smFn_tsum_replicate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ i, ∃ M : ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ (∀ p, ∀ f ∈ S, ‖Λ (List.replicate p i) f‖ ≤ M p * ∫ x in K, ‖f x‖ ∂μ) ∧ ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) → SmFn h b μ S K fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f := by
  first | exact @GlobalTheory.HCA.smFn_tsum_replicate | exact GlobalTheory.HCA.smFn_tsum_replicate | (intros; apply GlobalTheory.HCA.smFn_tsum_replicate <;> assumption)
end _root_.GlobalTheory.T
