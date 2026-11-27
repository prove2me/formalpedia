-- Prove2me | solution 1 for GlobalTheory.isoTransvection_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:31.273261+00:00
-- url     : https://prove2.me/submissions/9abd7714-494a-44c2-929b-511206f2cf2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_isoTransvection_form_apply_apply
import Theorems.Thm_GlobalTheory_isoTransvection_adjoint
import Theorems.Thm_GlobalTheory_isoTransvection_isometry
import Theorems.Thm_GlobalTheory_isoTransvection_sub_mem_smul
import Theorems.Thm_GlobalTheory_isoTransvection_image_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
namespace GlobalTheory
theorem _root_.solution {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M]
    [Module R M] (h : M →ₗ[R] M →ₗ⋆[R] R) (hh : ∀ u v, h v u = star (h u v))
    (x : M) (hx : h x x = 0) :
    (∀ b v, isoTransvectionHom h x hx (Multiplicative.ofAdd b) v = v + (b * h v x) • x) ∧
    (∀ b, isoTransvectionHom h x hx (Multiplicative.ofAdd b) = isoTransvection h x hx b) ∧
    (∀ b b', isoTransvection h x hx b * isoTransvection h x hx b'
      = isoTransvection h x hx (b + b')) ∧
    (∀ b, isoTransvection h x hx b x = x) ∧
    (∀ b v, h (isoTransvection h x hx b v) x = h v x) ∧
    (∀ b u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (b + star b) * h u x * h x v) ∧
    (∀ b u v, h (isoTransvection h x hx b u) v = h u (isoTransvection h x hx (star b) v)) ∧
    (Module.Free R M → Module.Finite R M →
      ∀ b, LinearMap.det (isoTransvection h x hx b : M →ₗ[R] M) = 1) ∧
    (∀ b, b + star b = 0 →
      ∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v) ∧
    (∀ (R₀ : Subring R) (L : Submodule R₀ M) (I : Ideal R₀) (b : R₀), x ∈ L →
      (∀ v ∈ L, h v x ∈ R₀) → b ∈ I →
        (∀ v ∈ L, isoTransvection h x hx b v - v ∈ I • L) ∧
          isoTransvection h x hx b '' (L : Set M) = L) := by
  refine ⟨fun _ _ => rfl, fun _ => rfl, isoTransvection.mul h x hx,
    isoTransvection.apply_self h x hx, isoTransvection.form_apply_self h x hx,
    isoTransvection.form_apply_apply x hx hh, isoTransvection.adjoint x hx hh,
    fun _ _ => isoTransvection.det_toLinearMap h x hx,
    fun b hb => isoTransvection.isometry x hx hh hb, fun R₀ L I b hxL hL hb => ?_⟩
  have hL' : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range := fun v hv => ⟨⟨_, hL v hv⟩, rfl⟩
  exact ⟨fun v hv => isoTransvection.sub_mem_smul h x hx hxL hL' hb hv,
    isoTransvection.image_eq h x hx hxL hL' b⟩
end GlobalTheory
