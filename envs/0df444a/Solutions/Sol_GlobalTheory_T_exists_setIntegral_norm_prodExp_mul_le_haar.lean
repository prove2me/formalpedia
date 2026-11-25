-- Prove2me | solution 1 for GlobalTheory.T.exists_setIntegral_norm_prodExp_mul_le_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:22:34.104317+00:00
-- url     : https://prove2.me/submissions/c9a5e941-68f4-4625-b5a5-b257f065b6d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaarStatement
import Theorems.Thm_GlobalTheory_setIntegral_norm_prodExp_mul_le_haar


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
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ ρ > 0, ∀ K₁ : Set G, IsCompact K₁ → ∃ (C : ℝ) (K₂ : Set G), 0 ≤ C ∧ IsCompact K₂ ∧ ∀ φ : G → ℂ, Continuous φ → ∀ y ∈ K₁, ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, ‖φ (h.prodExp b t * y)‖ ≤ C * ∫ x in K₂, ‖φ x‖ ∂μ := by
  first | exact @GlobalTheory.setIntegral_norm_prodExp_mul_le_haar | exact GlobalTheory.setIntegral_norm_prodExp_mul_le_haar | (intros; apply GlobalTheory.setIntegral_norm_prodExp_mul_le_haar <;> assumption)
end _root_.GlobalTheory.T
