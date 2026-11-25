-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_isometry_apply_eq_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:00:17.606215+00:00
-- url     : https://prove2.me/submissions/5f0d32c4-ae47-43c4-945b-d38e081122a8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_quasiReflection_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_quasiReflection
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_conj_toSesq_self
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
theorem _root_.solution [FiniteDimensional E V] (h : HermitianForm F E V)
    {x y : V} (hxy : h.toSesq x x = h.toSesq y y) (hd : h.toSesq x x - h.toSesq y x ≠ 0) :
    ∃ g : V ≃ₗ[E] V, (∀ z z', h.toSesq (g z) (g z') = h.toSesq z z') ∧ g x = y := by
  set d := h.toSesq x x - h.toSesq y x with hd_def
  have hcd : conj F E d = h.toSesq x x - h.toSesq x y := by
    rw [hd_def, map_sub, h.conj_toSesq_self, h.conj_toSesq]
  have hcd0 : conj F E d ≠ 0 := by
    intro h0; apply hd; rw [← conj_conj (F := F) d, h0, map_zero]
  have hww : d + conj F E d = h.toSesq (x - y) (x - y) := by
    rw [hcd, hd_def]
    simp only [map_sub, LinearMap.sub_apply]
    rw [← hxy]
    ring
  have hc : d⁻¹ + conj F E d⁻¹ = d⁻¹ * conj F E d⁻¹ * h.toSesq (x - y) (x - y) := by
    rw [map_inv₀, ← hww]
    field_simp
    ring
  refine ⟨h.equivOfIsometry _ (h.toSesq_quasiReflection hc), h.toSesq_quasiReflection hc, ?_⟩
  rw [equivOfIsometry_apply, quasiReflection_apply]
  have : h.toSesq (x - y) x = d := by rw [map_sub, LinearMap.sub_apply]
  rw [this, inv_mul_cancel₀ hd, one_smul]
  abel
end GroundTheory.Automorphic.HermitianForm
