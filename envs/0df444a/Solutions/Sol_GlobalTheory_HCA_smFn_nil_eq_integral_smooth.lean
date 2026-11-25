-- Prove2me | solution 1 for GlobalTheory.HCA.smFn_nil_eq_integral_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:42.298529+00:00
-- url     : https://prove2.me/submissions/4a8cfe68-de11-4cef-ba42-b543a814f7fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulConvolutionEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDixmierMalliavinDecompProdExpStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousLeftTranslateBoundedDerivFunctionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegrableDensityOfBoundByIntegralCompactAStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstFunctionalIntegralSmoothCompact
import Theorems.Thm_GlobalTheory_T_continuous_leftTranslate_boundedDerivFunctional
import Theorems.Thm_GlobalTheory_T_exists_dixmierMalliavin_decomp_prodExp
import Theorems.Thm_GlobalTheory_T_exists_integrable_density_of_bound_by_integral_on_compact
import Theorems.Thm_GlobalTheory_T_integral_mul_convolution_eq_alt
import Theorems.Thm_GlobalTheory_T_smooth_hasCompactSupport_conv_of_integrable_compact
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsTestFunction_continuous
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_smooth_density_prodExp_tsupport
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_locallyCompactSpace
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_mem_smoothFuns
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_secondCountableTopology
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
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
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∃ α : G → ℂ, h.IsSmoothFun α ∧ HasCompactSupport α ∧ ∀ f ∈ S, ∫ y, f y * α y ∂μ = Λ [] f := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hSc hSt K hK Λ hΛ
  haveI := hμ
  haveI : LocallyCompactSpace G := h.locallyCompactSpace
  haveI : SecondCountableTopology G := h.secondCountableTopology
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  obtain ⟨N, Λ', κ, hκ, hsum⟩ := GlobalTheory.T.exists_dixmierMalliavin_decomp_prodExp 𝔸 G 𝔤 h d b μ hμ S hSc hSt K hK ε hε d id Λ hΛ
  choose κ' hκ'sm hκ'cs _ hκ'int using fun m => hdens (κ m) (hκ m).2.1 (hκ m).2.2
  have hKμ : μ K < ⊤ := hK.measure_lt_top
  choose C hC using fun m => (hκ m).1.bdd []
  choose a ha using fun m => GlobalTheory.T.exists_integrable_density_of_bound_by_integral_on_compact G μ K hK hKμ S hSc (Λ' m []) (C m) ((hκ m).1.lin []) (hC m)
  have hκ'is : ∀ m, h.IsSmoothFun (κ' m) := fun m => hκ'sm m
  have hκ'c : ∀ m, Continuous (κ' m) := fun m => by
    letI := h.chartedSpace; exact (hκ'sm m).continuous
  have hconv := fun m => GlobalTheory.T.smooth_hasCompactSupport_conv_of_integrable_compact 𝔸 G 𝔤 h μ hμ K hK (κ' m) (a m) (hκ'is m) (hκ'cs m) (ha m).1 (ha m).2.1 (ha m).2.2.1
  refine ⟨fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ, ?_, ?_, ?_⟩
  · have e : (fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) =
        ∑ m, (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := by
      ext z; simp [Finset.sum_apply]
    rw [e]
    exact h.mem_smoothFuns.1 (Submodule.sum_mem (h.smoothFuns (F := ℂ)) fun m _ => h.mem_smoothFuns.2 (hconv m).1)
  · have e : (fun z => ∑ m, ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) =
        ∑ m, (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := by
      ext z; simp [Finset.sum_apply]
    rw [e]
    exact Finset.sum_induction _ HasCompactSupport (fun _ _ hu hv => hu.add hv) HasCompactSupport.zero
      fun m _ => (hconv m).2
  · intro f hf
    have hcc : ∀ m, Continuous (fun z => ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) := fun m => by
      letI := h.chartedSpace; exact (hconv m).1.continuous
    have hint : ∀ m, Integrable (fun z => f z * ∫ x, κ' m x * a m (x⁻¹ * z) ∂μ) μ := fun m =>
      ((hSc f hf).mul (hcc m)).integrable_of_hasCompactSupport (hconv m).2.mul_left
    calc ∫ y, f y * (∑ m, ∫ x, κ' m x * a m (x⁻¹ * y) ∂μ) ∂μ
        = ∑ m, ∫ y, f y * ∫ x, κ' m x * a m (x⁻¹ * y) ∂μ ∂μ := by
          simp_rw [Finset.mul_sum]; exact integral_finsetSum _ fun m _ => hint m
      _ = ∑ m, ∫ x, κ' m x * Λ' m [] (fun y => f (x * y)) ∂μ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [GlobalTheory.T.integral_mul_convolution_eq_alt G μ hμ K hK (κ' m) (a m) (hκ'c m) (hκ'cs m) (ha m).1 (ha m).2.1 (ha m).2.2.1 f (hSc f hf)]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          have hx := (ha m).2.2.2 _ (hSt f hf x)
          simp only at hx ⊢
          rw [hx]
      _ = ∑ m, ∫ t, κ m t * Λ' m [] (fun y => f (h.prodExp (fun k => b (id k)) t * y)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          exact hκ'int m _ (GlobalTheory.T.continuous_leftTranslate_boundedDerivFunctional 𝔸 G 𝔤 h d b μ hμ S hSc hSt K hK (Λ' m) (hκ m).1 [] f hf)
      _ = Λ [] f := (hsum f hf).symm
end GlobalTheory.HCA
