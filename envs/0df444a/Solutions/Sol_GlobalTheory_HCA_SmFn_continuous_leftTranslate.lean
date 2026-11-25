-- Prove2me | solution 1 for GlobalTheory.HCA.SmFn.continuous_leftTranslate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:18:40.261558+00:00
-- url     : https://prove2.me/submissions/63db2e20-1464-4749-af16-e954be0eb1bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_locallyCompactSpace
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_secondCountableTopology
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
namespace SmFn
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l, ∀ f ∈ S, Continuous fun x : G => Λ l fun y => f (x * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK Λ hΛ l f hf
  haveI := h.locallyCompactSpace
  haveI : SecondCountableTopology 𝔸ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology G := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨C, hC⟩ := hΛ.bdd l
  rw [continuous_iff_continuousAt]
  intro x₀
  have hfc := hS f hf
  have hcont : Continuous fun x : G => ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ :=
    continuous_parametric_integral_of_continuous
      (f := fun x y : G => ‖f (x * y) - f (x₀ * y)‖)
      (((hfc.comp (continuous_fst.mul continuous_snd)).sub
        (hfc.comp (continuous_const.mul continuous_snd))).norm) hK
  have h0 : Filter.Tendsto (fun x : G => C * ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ) (nhds x₀) (nhds 0) := by
    have := (hcont.const_mul C).tendsto x₀
    simpa using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) h0
  have h1 := hΛ.lin l _ (hL f hf x₀) _ (hL f hf x) (-1)
  have h2 := hC _ (S.add_mem (S.smul_mem (-1 : ℂ) (hL f hf x₀)) (hL f hf x))
  rw [h1] at h2
  simpa [neg_add_eq_sub] using h2
end SmFn
end GlobalTheory.HCA
