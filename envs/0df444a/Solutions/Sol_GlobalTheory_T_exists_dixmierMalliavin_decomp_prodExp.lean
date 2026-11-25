-- Prove2me | solution 1 for GlobalTheory.T.exists_dixmierMalliavin_decomp_prodExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:41:06.657897+00:00
-- url     : https://prove2.me/submissions/ae45dc9f-8717-4cc2-8aef-cae2b17e7a47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExpStatement
import Theorems.Thm_GlobalTheory_HCA_SmFn_exists_decomp_prodExp


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
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  first | exact @GlobalTheory.HCA.SmFn.exists_decomp_prodExp | exact GlobalTheory.HCA.SmFn.exists_decomp_prodExp | (intros; apply GlobalTheory.HCA.SmFn.exists_decomp_prodExp <;> assumption)
end _root_.GlobalTheory.T
