-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isometric_of_prod_ofUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:10.696255+00:00
-- url     : https://prove2.me/submissions/3b398edf-b3d5-45fe-b88c-c881922867c2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometry_apply_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj


attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [Algebra.IsSeparable F E] [FiniteDimensional E V₂]
    (h₁ : HermitianForm F E V₁) (h₂ : HermitianForm F E V₂) (a : Fˣ)
    (H : Isometric (h₁.prod (ofUnit (E := E) a)) (h₂.prod (ofUnit (E := E) a))) :
    Isometric h₁ h₂ := by
  obtain ⟨φ, hφ⟩ := H
  set hT := h₂.prod (ofUnit (E := E) a)
  set hS := h₁.prod (ofUnit (E := E) a)
  have hTe : ∀ (p : V₂) (t : E), hT.toSesq (0, 1) (p, t) = algebraMap F E a * t := by
    intro p t
    rw [prod_apply, ofUnit_apply, map_zero, LinearMap.zero_apply, map_one, zero_add, one_mul]
  have hSe : ∀ (p : V₁) (t : E), hS.toSesq (0, 1) (p, t) = algebraMap F E a * t := by
    intro p t
    rw [prod_apply, ofUnit_apply, map_zero, LinearMap.zero_apply, map_one, zero_add, one_mul]
  have ha : algebraMap F E (a : F) ≠ 0 := by simp
  have hu : hT.toSesq (φ (0, 1)) (φ (0, 1)) = hT.toSesq (0, 1) (0, 1) := by
    rw [hφ, hSe, hTe]
  have hu0 : hT.toSesq (φ (0, 1)) (φ (0, 1)) ≠ 0 := by rw [hu, hTe, mul_one]; exact ha
  obtain ⟨τ, hτ, hτu⟩ := hT.exists_isometry_apply_eq hu hu0
  set ψ := φ.trans τ with hψ_def
  have hψ : ∀ z z', hT.toSesq (ψ z) (ψ z') = hS.toSesq z z' := by
    intro z z'; simp only [hψ_def, LinearEquiv.trans_apply, hτ, hφ]
  have hψ1 : ψ (0, 1) = (0, 1) := by simp only [hψ_def, LinearEquiv.trans_apply, hτu]
  have hA : ∀ x : V₁, (ψ (x, 0)).2 = 0 := by
    intro x
    have h1 := hψ (0, 1) (x, 0)
    rw [hψ1, hSe, mul_zero] at h1
    have h2 : algebraMap F E a * (ψ (x, 0)).2 = 0 := by
      rw [← hTe (ψ (x, 0)).1 (ψ (x, 0)).2]; exact h1
    exact (mul_eq_zero.1 h2).resolve_left ha
  have hB : ∀ y : V₂, (ψ.symm (y, 0)).2 = 0 := by
    intro y
    have h1 := hψ (0, 1) (ψ.symm (y, 0))
    rw [hψ1, LinearEquiv.apply_symm_apply, hTe, mul_zero] at h1
    have h2 : algebraMap F E a * (ψ.symm (y, 0)).2 = 0 := by
      rw [← hSe (ψ.symm (y, 0)).1 (ψ.symm (y, 0)).2]; exact h1.symm
    exact (mul_eq_zero.1 h2).resolve_left ha
  have hA' : ∀ x : V₁, ψ (x, 0) = ((ψ (x, 0)).1, 0) := fun x => Prod.ext rfl (hA x)
  have hB' : ∀ y : V₂, ψ.symm (y, 0) = ((ψ.symm (y, 0)).1, 0) := fun y => Prod.ext rfl (hB y)
  let f : V₁ →ₗ[E] V₂ := LinearMap.fst E V₂ E ∘ₗ (ψ : V₁ × E →ₗ[E] V₂ × E) ∘ₗ LinearMap.inl E V₁ E
  let g : V₂ →ₗ[E] V₁ :=
    LinearMap.fst E V₁ E ∘ₗ (ψ.symm : V₂ × E →ₗ[E] V₁ × E) ∘ₗ LinearMap.inl E V₂ E
  have hfg : ∀ y, f (g y) = y := by
    intro y
    simp only [f, g, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
      LinearEquiv.coe_coe]
    rw [← hB', LinearEquiv.apply_symm_apply]
  have hgf : ∀ x, g (f x) = x := by
    intro x
    simp only [f, g, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
      LinearEquiv.coe_coe]
    rw [← hA', LinearEquiv.symm_apply_apply]
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf), fun x y => ?_⟩
  simp only [LinearEquiv.ofLinear_apply, f, LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.fst_apply, LinearEquiv.coe_coe]
  have h1 := hψ (x, 0) (y, 0)
  rw [hA' x, hA' y, prod_apply, prod_apply] at h1
  have z1 : (ofUnit (E := E) a).toSesq (0 : E) 0 = 0 := by
    rw [ofUnit_apply, map_zero, zero_mul, zero_mul]
  change h₂.toSesq _ _ + (ofUnit (E := E) a).toSesq 0 0 =
    h₁.toSesq x y + (ofUnit (E := E) a).toSesq 0 0 at h1
  rw [z1, add_zero, add_zero] at h1
  exact h1
end GroundTheory.Automorphic.HermitianForm
