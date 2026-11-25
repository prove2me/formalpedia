-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.exists_expChart_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:17.957942+00:00
-- url     : https://prove2.me/submissions/e5254894-4e8d-430f-8c78-0bf8e7105527

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
import Theorems.Thm_GroundTheory_Automorphic_continuous_expChartProd
import Theorems.Thm_GroundTheory_Automorphic_analyticOnNhd_expChartFlow
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_ball_coordEquiv_mem_nhd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_expChartFlow
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expChartFlow_zero
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expChartProd_zero_mem_nhdOne
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_expChartFlow
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_coordEquiv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
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
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∃ c : 𝔤 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ X, AnalyticOnNhd ℝ (c X) (Metric.ball 0 r)) ∧
      (∀ X, c X 0 = (coordEquiv b).symm X) ∧
      ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (g : G),
        ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
          h.rightDeriv X f (g * h.expG (coordEquiv b x)) =
            fderiv ℝ (fun y => f (g * h.expG (coordEquiv b y))) x (c X x) := by
  obtain ⟨r, hr, hball⟩ := h.exists_ball_coordEquiv_mem_nhd b
  refine ⟨r, hr, expChartCoeff b, ?_, ?_, ?_⟩
  ·
    intro X x hx
    have hS : (x, (0 : ℝ)) ∈ expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target :=
      h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X (hball x hx))
    have hD := (analyticOnNhd_expChartFlow b X).fderiv (𝕜 := ℝ) _ hS
    have hinl : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) x :=
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ).analyticAt x
    have hD' : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (expChartFlow b X) (y, 0)) x :=
      AnalyticAt.comp (g := fderiv ℝ (expChartFlow b X))
        (f := fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) hD hinl
    have hap := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d))
      ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))).analyticAt (fderiv ℝ (expChartFlow b X) (x, 0))
    exact AnalyticAt.comp (f := fun y : EuclideanSpace ℝ (Fin d) => fderiv ℝ (expChartFlow b X) (y, 0))
      hap hD'
  ·
    intro X
    have h0 : ((coordEquiv b (0 : EuclideanSpace ℝ (Fin d)) : 𝔤) : 𝔸) ∈ h.nhd := by
      simp only [map_zero, ZeroMemClass.coe_zero]; exact h.zero_mem_nhd
    have hd := h.hasDerivAt_expChartFlow b X h0
    have hev : (fun t : ℝ => expChartFlow b X (0, t)) =ᶠ[𝓝 0]
        fun t : ℝ => t • (coordEquiv b).symm X := by
      have hc : Continuous (fun t : ℝ => t • (X : 𝔸)) := continuous_id.smul continuous_const
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t • (X : 𝔸) ∈ h.nhd := by
        have h1 := hc.continuousAt (x := 0)
        rw [ContinuousAt, zero_smul] at h1
        exact h1 (h.isOpen_nhd.mem_nhds h.zero_mem_nhd)
      filter_upwards [this] with t ht
      simp only [expChartFlow, expChartProd, map_zero, ZeroMemClass.coe_zero, exp_zero, one_mul]
      rw [h.symm_exp ht, show t • (X : 𝔸) = ((t • X : 𝔤) : 𝔸) from rfl, subspaceProj_coe, map_smul]
    have hd2 : HasDerivAt (fun t : ℝ => t • (coordEquiv b).symm X) ((coordEquiv b).symm X) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((coordEquiv b).symm X)
    exact hd.unique (hd2.congr_of_eventuallyEq hev)
  ·
    intro X f hf g x hx
    have hxN := hball x hx
    set u : EuclideanSpace ℝ (Fin d) → ℂ := fun y => f (g * h.expG (coordEquiv b y)) with hu
    have hud : Differentiable ℝ u := (h.contDiff_comp_coordEquiv hf g b).differentiable (by simp)
    have hφ := h.hasDerivAt_expChartFlow b X hxN
    have h1 : HasDerivAt (fun t : ℝ => u (expChartFlow b X (x, t)))
        (fderiv ℝ u x (expChartCoeff b X x)) 0 := by
      have := (hud (expChartFlow b X (x, 0))).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hφ
      rw [h.expChartFlow_zero b X hxN] at this
      exact this
    have h2 := h.hasDerivAt_rightDeriv hf X (g * h.expG (coordEquiv b x))
    have hev : (fun t : ℝ => f (g * h.expG (coordEquiv b x) * h.expG (t • X))) =ᶠ[𝓝 0]
        fun t : ℝ => u (expChartFlow b X (x, t)) := by
      have hc : Continuous (fun t : ℝ => expChartProd b X (x, t)) :=
        (continuous_expChartProd b X).comp (continuous_const.prodMk continuous_id)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), expChartProd b X (x, t) ∈ h.nhdOne :=
        hc.continuousAt.preimage_mem_nhds
          (h.isOpen_nhdOne.mem_nhds (h.expChartProd_zero_mem_nhdOne b X hxN))
      filter_upwards [this] with t ht
      simp only [hu]
      rw [h.expG_expChartFlow b X ht, mul_assoc]
    exact h2.unique (h1.congr_of_eventuallyEq hev)
end GroundTheory.Automorphic.IsExpLieAlgebra
