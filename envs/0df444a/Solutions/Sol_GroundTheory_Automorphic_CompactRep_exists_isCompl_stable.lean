-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactRep.exists_isCompl_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:20.892364+00:00
-- url     : https://prove2.me/submissions/c78650b1-9ea1-4133-9153-4a48224f4c9f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
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
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open MeasureTheory Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {σ : Representation ℂ K W}
namespace GroundTheory.Automorphic.CompactRep
theorem _root_.solution (hσ : Representation.HasContinuousCoeff σ) (U : Submodule ℂ W)
    (hU : ∀ k, ∀ u ∈ U, σ k u ∈ U) :
    ∃ C : Submodule ℂ W, IsCompl U C ∧ ∀ k, ∀ c ∈ C, σ k c ∈ C := by
  classical
  borelize K
  let K₀ : TopologicalSpace.PositiveCompacts K :=
    ⟨⟨univ, isCompact_univ⟩, by simp [interior_univ]⟩
  set μ : Measure K := Measure.haarMeasure K₀
  have hμ1 : μ univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := K₀)
    simpa [K₀] using this
  haveI : IsProbabilityMeasure μ := ⟨hμ1⟩
  set d := finrank ℂ W
  let b := Module.finBasis ℂ W
  let e : W ≃ₗ[ℂ] (Fin d → ℂ) := b.equivFun

  let S : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) := fun k =>
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ σ k ∘ₗ e.symm.toLinearMap)
  have hSapply : ∀ k w, S k (e w) = e (σ k w) := fun k w => by
    simp [S]
  have hSmul : ∀ a c, S (a * c) = (S a).comp (S c) := fun a c => by
    ext x : 1
    simp [S, map_mul]
  have hS : Continuous S := by
    refine continuous_clm_apply.2 fun y => continuous_pi fun i => ?_
    have := hσ (b.coord i) (e.symm y)
    refine this.congr fun k => ?_
    simp [S, e, Basis.equivFun_apply, Basis.coord_apply]

  obtain ⟨C₀, hC₀⟩ := U.exists_isCompl
  let p : W →ₗ[ℂ] W := U.subtype ∘ₗ Submodule.projectionOnto U C₀ hC₀
  have hpU : ∀ u ∈ U, p u = u := fun u hu => by
    show ((Submodule.projectionOnto U C₀ hC₀ u : U) : W) = u
    rw [Submodule.projectionOnto_apply_of_mem_left _ hu]
  have hpmem : ∀ w, p w ∈ U := fun w => Subtype.prop _
  let P₀ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ p ∘ₗ e.symm.toLinearMap)
  have hP₀ : ∀ w, P₀ (e w) = e (p w) := fun w => by simp [P₀]
  let f : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) := fun k => (S k).comp (P₀.comp (S k⁻¹))
  have hf : Continuous f := hS.clm_comp (continuous_const.clm_comp (hS.comp continuous_inv))
  have hfi : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfx : ∀ x, Integrable (fun k => f k x) μ := fun x =>
    (hf.clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfapply : ∀ k w, f k (e w) = e (σ k (p (σ k⁻¹ w))) := fun k w => by
    simp only [f, ContinuousLinearMap.comp_apply, hSapply, hP₀]
  set P := ∫ k, f k ∂μ

  have hPU : ∀ u ∈ U, P (e u) = e u := by
    intro u hu
    rw [ContinuousLinearMap.integral_apply hfi]
    have : ∀ k, f k (e u) = e u := fun k => by
      rw [hfapply, hpU _ (hU _ _ hu), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    simp only [this, integral_const]
    rw [show μ.real univ = 1 by simp [Measure.real, hμ1], one_smul]

  let R : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (LinearMap.id - p) ∘ₗ e.symm.toLinearMap)
  have hPmem : ∀ w, e.symm (P (e w)) ∈ U := by
    intro w
    have h1 : R (P (e w)) = 0 := by
      rw [ContinuousLinearMap.integral_apply hfi, ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]
      have : ∀ k, R (f k (e w)) = 0 := fun k => by
        rw [hfapply]
        simp only [R, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
          LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.sub_apply,
          LinearMap.id_apply, hpU _ (hU _ _ (hpmem _)), sub_self, map_zero]
      simp [this]
    have h2 : e.symm (P (e w)) - p (e.symm (P (e w))) = 0 := by
      have := congrArg e.symm h1
      simpa [R] using this
    rw [sub_eq_zero] at h2
    rw [h2]
    exact hpmem _

  have hPcomm : ∀ g x, P (S g x) = S g (P x) := by
    intro g x
    rw [ContinuousLinearMap.integral_apply hfi, ContinuousLinearMap.integral_apply hfi,
      ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]
    have h1 : ∀ k, f k (S g x) = S k (P₀ (S (k⁻¹ * g) x)) := by
      intro k
      rw [hSmul]
      rfl
    have h2 : ∀ k, S g (f k x) = S (g * k) (P₀ (S ((g * k)⁻¹ * g) x)) := by
      intro k
      rw [hSmul g k, show (g * k)⁻¹ * g = k⁻¹ by group]
      rfl
    simp only [h1, h2]
    exact (integral_mul_left_eq_self (μ := μ) (fun y => S y (P₀ (S (y⁻¹ * g) x))) g).symm

  let Q : W →ₗ[ℂ] U := LinearMap.codRestrict U
    (e.symm.toLinearMap ∘ₗ P.toLinearMap ∘ₗ e.toLinearMap) fun w => hPmem w
  have hQ : ∀ x : U, Q x = x := fun x => Subtype.ext (by
    simp [Q, hPU _ x.2])
  refine ⟨LinearMap.ker Q, LinearMap.isCompl_of_proj hQ, fun k c hc => ?_⟩
  rw [LinearMap.mem_ker] at hc ⊢
  have hc' : P (e c) = 0 := by
    have := congrArg (fun y : U => e (y : W)) hc
    simpa [Q] using this
  refine Subtype.ext ?_
  simp only [Q, LinearMap.codRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, ContinuousLinearMap.coe_coe, ZeroMemClass.coe_zero]
  rw [← hSapply, hPcomm, hc', map_zero, map_zero]
end GroundTheory.Automorphic.CompactRep
