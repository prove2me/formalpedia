-- Prove2me | solution 1 for GlobalTheory.ExpCoordFrame.leftInvariant_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:32.078422+00:00
-- url     : https://prove2.me/submissions/e8ba9dfd-bc05-498c-8293-acdf99b50b1e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrame
import Theorems.Thm_GlobalTheory_ExpCoordFrame_contDiffAt_psi
import Theorems.Thm_GlobalTheory_ExpCoordFrame_psi_zero
import Theorems.Thm_GlobalTheory_ExpCoordFrame_psi_origin_eventually
import Theorems.Thm_GlobalTheory_ExpCoordFrame_expG_psi
import Theorems.Thm_GlobalTheory_ExpCoordFrame_differentiableAt_psi
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_coordEquiv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_coordEquiv_zero
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
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpCoordFrame
open NormedSpace Filter Topology
namespace GlobalTheory.ExpCoordFrame
theorem _root_.solution (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤)
    (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∃ c : 𝔤 → Fin d → E d → ℝ, (∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧
      (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧
      ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r,
        h.rightDeriv X f (h.expG (coordEquiv b (x))) =
          ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j) := by
  obtain ⟨r₁, hr₁, hball₁⟩ : ∃ r₁ > 0,
      Metric.ball (0 : E d) r₁ ⊆ {x | ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd} := by
    have ho : IsOpen {x : E d | ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd} :=
      h.isOpen_nhd.preimage (continuous_subtype_val.comp (coordEquiv b).continuous)
    exact Metric.isOpen_iff.1 ho 0 (by simpa [coordEquiv_zero] using h.zero_mem_nhd)
  set A : E d → 𝔤 →L[ℝ] E d := fun x => fderiv ℝ (psi b x) 0 with hA
  have hAx : ∀ x ∈ Metric.ball (0 : E d) r₁, ContDiffAt ℝ ∞ A x := fun x hx =>
    (contDiffAt_psi b x (h.nhd_subset (hball₁ hx))).fderiv (contDiffAt_const (c := (0 : 𝔤)))
      (by simp)
  set B : E d → E d →L[ℝ] E d := fun x => (A x).comp (coordEquiv b : E d →L[ℝ] 𝔤) with hB
  have hA0 : A 0 = ((coordEquiv b).symm : 𝔤 →L[ℝ] E d) := by
    simp only [hA]
    rw [(psi_origin_eventually b).fderiv_eq, ContinuousLinearEquiv.fderiv]
  have hB0 : IsUnit (B 0) := by
    have : B 0 = 1 := by
      ext v; simp [hB, hA0]
    rw [this]; exact isUnit_one
  have hBc : ContinuousAt B 0 :=
    ((hAx 0 (Metric.mem_ball_self hr₁)).clm_comp contDiffAt_const).continuousAt
  have hU : {x | IsUnit (B x)} ∈ 𝓝 (0 : E d) := hBc.preimage_mem_nhds (Units.isOpen.mem_nhds hB0)
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun X j x => A x X j, ?_, ?_, ?_⟩
  · intro X j x hx
    have hx1 : x ∈ Metric.ball (0 : E d) r₁ := Metric.ball_subset_ball (min_le_left _ _) hx
    exact ((EuclideanSpace.proj j : E d →L[ℝ] ℝ).contDiff.comp_contDiffAt x
      ((hAx x hx1).clm_apply contDiffAt_const)).contDiffWithinAt
  · intro x hx ξ hξ
    by_contra hcon
    push_neg at hcon
    have hx2 : x ∈ Metric.ball (0 : E d) r₂ := Metric.ball_subset_ball (min_le_right _ _) hx
    obtain ⟨u, hu⟩ : IsUnit (B x) := hball₂ hx2
    set ℓ : 𝔤 →L[ℝ] ℝ := ∑ j, ξ j • ((EuclideanSpace.proj j : E d →L[ℝ] ℝ).comp (A x)) with hℓ
    have hℓ0 : (ℓ : 𝔤 →ₗ[ℝ] ℝ) = 0 := b.ext fun i => by
      have := hcon i
      simp only [hℓ, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_coe,
        Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, LinearMap.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; rfl
    set X : 𝔤 := coordEquiv b (((u⁻¹ : (E d →L[ℝ] E d)ˣ) : E d →L[ℝ] E d) ξ)
    have hX : A x X = ξ := by
      have e1 : ((u : E d →L[ℝ] E d) * ↑u⁻¹) ξ = ξ := by rw [u.mul_inv]; rfl
      rw [hu] at e1; exact e1
    have h1 : ℓ X = ∑ j, ξ j * ξ j := by
      simp only [hℓ, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, hX]
      rfl
    have h2 : ℓ X = 0 := by
      have := congrArg (fun L : 𝔤 →ₗ[ℝ] ℝ => L X) hℓ0
      simpa using this
    apply hξ
    have hs : ∑ j, ξ j * ξ j = 0 := h1.symm.trans h2
    ext j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (ξ j))).1 hs j
      (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 this
  · intro f hf X x hx
    have hx1 : x ∈ Metric.ball (0 : E d) r₁ := Metric.ball_subset_ball (min_le_left _ _) hx
    have hxN : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd := hball₁ hx1
    have hxS := h.nhd_subset hxN
    set φ : E d → ℂ := fun y => f (h.expG (coordEquiv b y)) with hφ
    have hφd : Differentiable ℝ φ := by
      have := h.contDiff_comp_coordEquiv hf 1 b
      simp only [one_mul] at this
      exact this.differentiable (by simp)
    have hev : (fun Y : 𝔤 => f (h.expG (coordEquiv b x) * h.expG Y)) =ᶠ[𝓝 0] φ ∘ psi b x := by
      filter_upwards [expG_psi h b x hxN] with Y hY
      simp [φ, hY]
    have hdiff : DifferentiableAt ℝ (psi b x) 0 := differentiableAt_psi b x hxS
    have key : h.rightDeriv X f (h.expG (coordEquiv b x)) = fderiv ℝ φ x (A x X) := by
      unfold IsExpLieAlgebra.rightDeriv
      rw [hev.fderiv_eq, fderiv_comp (0 : 𝔤) (by rw [psi_zero b x hxS]; exact hφd _) hdiff,
        psi_zero b x hxS]
      rfl
    rw [key]
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (A x X)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Complex.real_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    rfl
end GlobalTheory.ExpCoordFrame
