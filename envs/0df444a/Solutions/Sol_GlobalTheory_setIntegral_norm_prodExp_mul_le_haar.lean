-- Prove2me | solution 1 for GlobalTheory.setIntegral_norm_prodExp_mul_le_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:32.939002+00:00
-- url     : https://prove2.me/submissions/ac7824d2-d6e8-4bfe-bc67-e5fbcdb0ef18

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaar
import Theorems.Thm_GlobalTheory_T_haar_lintegral_mul_right_le_alt
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_prodExp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_smooth_density_prodExp_tsupport
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isClosed
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_locallyCompactSpace
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_secondCountableTopology
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
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
open scoped Pointwise
namespace GlobalTheory
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∃ ρ > 0, ∀ K₁ : Set G, IsCompact K₁ → ∃ (C : ℝ) (K₂ : Set G), 0 ≤ C ∧ IsCompact K₂ ∧ ∀ φ : G → ℂ, Continuous φ → ∀ y ∈ K₁, ∫ t in Metric.closedBall (0 : Fin d → ℝ) ρ, ‖φ (h.prodExp b t * y)‖ ≤ C * ∫ x in K₂, ‖φ x‖ ∂μ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ
  haveI := hμ
  haveI : LocallyCompactSpace G := h.locallyCompactSpace
  haveI : SecondCountableTopology 𝔸ˣ := Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  haveI : SecondCountableTopology G := Topology.IsInducing.subtypeVal.secondCountableTopology
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp_tsupport μ b
  refine ⟨ε / 2, by positivity, fun K₁ hK₁ => ?_⟩
  let β : ContDiffBump (0 : Fin d → ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  set K : (Fin d → ℝ) → ℂ := fun t => ((β t : ℝ) : ℂ) with hKdef
  have hK : ContDiff ℝ ∞ K := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hKs : tsupport K ⊆ Metric.closedBall 0 ε := by
    have : tsupport K ⊆ tsupport β := tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) _
    rw [β.tsupport_eq] at this
    exact this
  obtain ⟨κ, hκs, hκc, -, hκint⟩ := hdens K hK hKs
  have hκcont : Continuous κ := by
    letI := h.chartedSpace
    exact hκs.continuous
  obtain ⟨M, hM⟩ := hκc.exists_bound_of_continuous hκcont
  have hK₂ : IsCompact (tsupport κ * K₁) := IsCompact.mul hκc hK₁
  obtain ⟨B, hB⟩ := GlobalTheory.T.haar_lintegral_mul_right_le_alt G μ hμ K₁ hK₁
  refine ⟨max M 0 * B, tsupport κ * K₁, by positivity, hK₂, fun φ hφ y hy => ?_⟩
  set K₂ := tsupport κ * K₁ with hK₂def
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  set f : (Fin d → ℝ) → ℝ := fun t => ‖φ (P t * y)‖ with hfdef
  have hfc : Continuous f := (hφ.comp (hPc.mul continuous_const)).norm
  set ψ : G → ℂ := fun x => ((‖φ (x * y)‖ : ℝ) : ℂ) with hψdef
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp (hφ.comp (continuous_id.mul continuous_const)).norm

  have h1 : ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), f t ≤ ∫ t, β t * f t := by
    have e : ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), f t
        = ∫ t in Metric.closedBall (0 : Fin d → ℝ) (ε / 2), β t * f t := by
      refine setIntegral_congr_fun measurableSet_closedBall fun t ht => ?_
      rw [β.one_of_mem_closedBall ht, one_mul]
    rw [e]
    refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun t => mul_nonneg β.nonneg (norm_nonneg _))
    exact (β.continuous.mul hfc).integrable_of_hasCompactSupport β.hasCompactSupport.mul_right

  have h2 : ∫ t, β t * f t = (∫ x, κ x * ψ x ∂μ).re := by
    rw [hκint ψ hψc]
    have : (fun t => K t * ψ (P t)) = fun t => (((β t * f t : ℝ)) : ℂ) := by
      funext t; simp [hKdef, hψdef, hfdef]
    rw [this, integral_complex_ofReal, Complex.ofReal_re]

  have h3 : (∫ x, κ x * ψ x ∂μ).re ≤ ∫ x, ‖κ x * ψ x‖ ∂μ :=
    (Complex.re_le_norm _).trans (norm_integral_le_integral_norm _)

  set g : G → ENNReal := K₂.indicator fun z => ‖φ z‖ₑ with hgdef
  have hg : Measurable g := hφ.enorm.measurable.indicator hK₂.isClosed.measurableSet
  set L := ∫⁻ x in K₂, ‖φ x‖ₑ ∂μ with hLdef
  have hL : L < ⊤ := (hφ.continuousOn.integrableOn_compact hK₂).hasFiniteIntegral
  have hgL : ∫⁻ x, g x ∂μ = L := lintegral_indicator hK₂.isClosed.measurableSet _
  have hpt : ∀ x, ‖κ x * ψ x‖ₑ ≤ ENNReal.ofReal (max M 0) * g (x * y) := by
    intro x
    by_cases hx : x ∈ tsupport κ
    · have hxy : x * y ∈ K₂ := Set.mul_mem_mul hx hy
      rw [hgdef, Set.indicator_of_mem hxy, enorm_mul]
      gcongr
      · rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal ((hM x).trans (le_max_left _ _))
      · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        apply le_of_eq
        congr 1
        simp [hψdef]
    · have : κ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have h4l : ∫⁻ x, ‖κ x * ψ x‖ₑ ∂μ ≤ ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) := by
    calc ∫⁻ x, ‖κ x * ψ x‖ₑ ∂μ ≤ ∫⁻ x, ENNReal.ofReal (max M 0) * g (x * y) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal (max M 0) * ∫⁻ x, g (x * y) ∂μ :=
          lintegral_const_mul _ (hg.comp (measurable_id.mul_const y))
      _ ≤ ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) := by
          gcongr
          rw [← hgL]
          exact hB y hy g hg
  have h4 : ∫ x, ‖κ x * ψ x‖ ∂μ ≤ max M 0 * B * ∫ x in K₂, ‖φ x‖ ∂μ := by
    rw [integral_norm_eq_lintegral_enorm (f := fun x => κ x * ψ x) (hκcont.mul hψc).aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hφ.aestronglyMeasurable]
    have hfin : ENNReal.ofReal (max M 0) * ((B : ENNReal) * L) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hL.ne)
    refine (ENNReal.toReal_mono hfin h4l).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_right _ _),
      ENNReal.coe_toReal, mul_assoc]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h4
end GlobalTheory
