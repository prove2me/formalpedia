-- Prove2me | solution 1 for GlobalTheory.ConvSmooth.conv_smooth_compactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:58.013941+00:00
-- url     : https://prove2.me/submissions/6243d675-cf02-49d5-bafb-4ff155ca4048

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupport
import Theorems.Thm_GlobalTheory_ConvSmooth_secondCountable_units
import Theorems.Thm_GlobalTheory_ConvSmooth_isSmoothFun_density
import Theorems.Thm_GlobalTheory_ConvSmooth_posPart_decomp
import Theorems.Thm_GlobalTheory_T_lintegral_inv_le_of_support_compact_alt
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsTestFunction_continuous
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_locallyCompactSpace
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_mem_smoothFuns
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
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ConvSmooth
namespace GlobalTheory.ConvSmooth
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K : Set G, IsCompact K → ∀ κ a : G → ℂ, h.IsSmoothFun κ → HasCompactSupport κ → Measurable a → Integrable a μ → (∀ x ∉ K, a x = 0) → h.IsSmoothFun (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) ∧ HasCompactSupport (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ μ hμ K hK κ a hκ hκc ha hai haK
  haveI := h.locallyCompactSpace
  haveI := secondCountable_units 𝔸
  haveI : SecondCountableTopology G := Topology.IsInducing.subtypeVal.secondCountableTopology
  constructor
  · set b : G → ℂ := fun y => a y⁻¹ with hb
    have hbm : Measurable b := ha.comp measurable_inv
    have hbK : ∀ y ∉ K⁻¹, b y = 0 := fun y hy => haK _ (by simpa [Set.mem_inv] using hy)
    have hbi : Integrable b μ := by
      obtain ⟨B, hB⟩ := GlobalTheory.T.lintegral_inv_le_of_support_compact_alt G μ hμ K hK
      refine ⟨hbm.aestronglyMeasurable, ?_⟩
      have h1 := hB (fun x => ‖a x‖ₑ) ha.enorm (fun x hx => by simp [haK x hx])
      exact lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.coe_lt_top hai.2)
    have hcv : ∀ z, ∫ x, κ x * a (x⁻¹ * z) ∂μ = ∫ y, κ (z * y) * b y ∂μ := by
      intro z
      rw [← integral_mul_left_eq_self (fun x => κ x * a (x⁻¹ * z)) z]
      congr 1; funext y; simp [hb, mul_inv_rev, mul_assoc]
    have hκcont : Continuous κ := by
      letI := h.chartedSpace
      exact ContMDiff.continuous hκ
    obtain ⟨C, hC⟩ := hκcont.bounded_above_of_compact_support hκc
    have hre : Integrable (fun y => (b y).re) μ := by simpa using hbi.re
    have him : Integrable (fun y => (b y).im) μ := by simpa using hbi.im
    have hpos : ∀ f : G → ℝ, Integrable f μ → Integrable (fun y => ((Real.toNNReal (f y) : NNReal) : ℝ)) μ :=
      fun f hf => by simpa [Real.coe_toNNReal'] using hf.pos_part
    have hK' : IsCompact K⁻¹ := hK.inv
    have hre' : Integrable (fun y => -(b y).re) μ := hre.neg
    have him' : Integrable (fun y => -(b y).im) μ := him.neg
    have S : ∀ f : G → ℝ, Measurable f → Integrable f μ → (∀ y ∉ K⁻¹, f y = 0) →
        h.IsSmoothFun (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ) ∂μ) :=
      fun f hfm hf hf0 => isSmoothFun_density h μ hK' hκ hfm.real_toNNReal (hpos f hf)
        (fun y hy => by simp [hf0 y hy])
    have hbre : ∀ y ∉ K⁻¹, (b y).re = 0 := fun y hy => by simp [hbK y hy]
    have hbim : ∀ y ∉ K⁻¹, (b y).im = 0 := fun y hy => by simp [hbK y hy]
    have s1 := S _ (Complex.measurable_re.comp hbm) hre hbre
    have s2 := S _ (Complex.measurable_re.comp hbm).neg hre' (fun y hy => by simp [hbre y hy])
    have s3 := S _ (Complex.measurable_im.comp hbm) him hbim
    have s4 := S _ (Complex.measurable_im.comp hbm).neg him' (fun y hy => by simp [hbim y hy])
    have hI : ∀ (z : G) (f : G → ℝ), Integrable f μ →
        Integrable (fun y => κ (z * y) * (((Real.toNNReal (f y) : NNReal) : ℝ) : ℂ)) μ := by
      intro z f hf
      refine ((hpos f hf).ofReal (𝕜 := ℂ)).bdd_mul (hκcont.comp (continuous_const_mul z)).aestronglyMeasurable (ae_of_all _ fun y => hC _)
    have hsum : (fun z => ∫ x, κ x * a (x⁻¹ * z) ∂μ) =
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ) ∂μ) +
        Complex.I • ((fun z => ∫ y, κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) ∂μ) -
        (fun z => ∫ y, κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ) ∂μ)) := by
      funext z
      rw [hcv z]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e : (fun y => κ (z * y) * b y) = fun y =>
          (κ (z * y) * (((Real.toNNReal (b y).re : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).re) : NNReal) : ℝ) : ℂ)) +
          Complex.I * (κ (z * y) * (((Real.toNNReal (b y).im : NNReal) : ℝ) : ℂ) -
            κ (z * y) * (((Real.toNNReal (-(b y).im) : NNReal) : ℝ) : ℂ)) := by
        funext y
        conv_lhs => rw [posPart_decomp (b y)]
        ring
      rw [e, integral_add ?_ ?_, integral_sub ?_ ?_, integral_const_mul, integral_sub ?_ ?_]
      all_goals first
        | exact hI z _ hre | exact hI z _ hre' | exact hI z _ him | exact hI z _ him'
        | exact (hI z _ hre).sub (hI z _ hre')
        | exact ((hI z _ him).sub (hI z _ him')).const_mul _
    rw [← h.mem_smoothFuns, hsum]
    exact Submodule.add_mem _ (Submodule.sub_mem _ s1 s2)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ s3 s4))
  · refine HasCompactSupport.intro (hκc.mul hK) fun z hz => ?_
    have : (fun x => κ x * a (x⁻¹ * z)) = 0 := by
      funext x
      by_cases hx : x ∈ tsupport κ
      · have : x⁻¹ * z ∉ K := fun h' => hz ⟨x, hx, x⁻¹ * z, h', by simp⟩
        simp [haK _ this]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp only [this]; exact integral_zero' ..
end GlobalTheory.ConvSmooth
