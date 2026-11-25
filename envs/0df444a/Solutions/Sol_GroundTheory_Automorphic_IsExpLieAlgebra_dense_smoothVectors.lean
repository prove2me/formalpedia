-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.dense_smoothVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:58.159846+00:00
-- url     : https://prove2.me/submissions/77ea67a8-732a-4f11-b105-c405bbaeaec3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Theorems.Thm_GroundTheory_Automorphic_secondCountableTopology_subgroup_units
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsTestFunction_continuous
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_integrable_smul_orbit
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_integrated
import Theorems.Thm_GroundTheory_Automorphic_BanachRep_continuous_orbit
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_locallyCompactSpace
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
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
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]
omit [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution : Dense (h.smoothVectors π : Set E) := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haveI := h.locallyCompactSpace
  haveI := secondCountableTopology_subgroup_units G
  set μ : Measure G := Measure.haar
  rw [Metric.dense_iff]
  intro v r hr
  have hU : (fun g => π g v) ⁻¹' ball v (r / 2) ∈ 𝓝 (1 : G) :=
    (π.continuous_orbit v).continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds v (half_pos hr))
  letI := h.chartedSpace
  haveI := h.isManifold ∞
  obtain ⟨b, -, hbU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, 𝔤)) (1 : G)).mem_iff.1 hU
  set c : ℝ := ∫ g, b g ∂μ with hcdef
  have hc : 0 < c := b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    b.hasCompactSupport (fun x => b.nonneg) (x := 1) (by rw [b.eq_one]; exact one_ne_zero)
  set f : G → ℂ := fun g => ((c⁻¹ * b g : ℝ) : ℂ) with hfdef
  have hsupp : Function.support f ⊆ Function.support b := by
    intro g hg hb
    apply hg
    simp [hfdef, hb]
  have hf : h.IsTestFunction f := by
    refine ⟨?_, b.hasCompactSupport.mono hsupp⟩
    set L : ℝ →L[ℝ] ℂ := c⁻¹ • Complex.ofRealCLM
    have e : f = L ∘ b := by funext g; simp [L, hfdef]
    rw [e]
    exact L.contDiff.comp_contMDiff b.contMDiff
  have hfint : Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hf.2
  have hint1 : ∫ g, f g ∂μ = 1 := by
    show ∫ g, ((c⁻¹ * b g : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne', Complex.ofReal_one]
  refine ⟨π.integrated μ f v, ?_, h.isSmoothVector_integrated π μ hf v⟩
  rw [mem_ball, dist_eq_norm]
  have e : π.integrated μ f v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub (h.integrable_smul_orbit π μ hf v) (hfint.smul_const v), integral_smul_const,
      hint1, one_smul]
    rfl
  rw [e]
  have hbound : ∀ g, ‖f g • (π g v - v)‖ ≤ (c⁻¹ * b g) * (r / 2) := by
    intro g
    rw [norm_smul, hfdef, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hc.le) b.nonneg)]
    by_cases hb : b g = 0
    · simp [hb]
    · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (inv_nonneg.2 hc.le) b.nonneg)
      have h2 := hbU (subset_tsupport _ hb)
      rw [mem_preimage, mem_ball, dist_eq_norm] at h2
      exact h2.le
  calc ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, (c⁻¹ * b g) * (r / 2) ∂μ :=
        norm_integral_le_of_norm_le ((b.continuous.integrable_of_hasCompactSupport
          b.hasCompactSupport).const_mul c⁻¹ |>.mul_const _) (Eventually.of_forall hbound)
    _ = r / 2 := by rw [integral_mul_const, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne', one_mul]
    _ < r := half_lt_self hr
end GroundTheory.Automorphic.IsExpLieAlgebra
