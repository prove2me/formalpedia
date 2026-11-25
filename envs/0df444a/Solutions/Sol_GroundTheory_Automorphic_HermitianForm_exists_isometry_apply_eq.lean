-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_isometry_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:42.547286+00:00
-- url     : https://prove2.me/submissions/0b35dd5c-4971-48e4-ab88-31fb38db3508

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometry_apply_eq_of_ne
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_exists_mul_conj_eq_one_ne_one
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
theorem _root_.solution [Algebra.IsSeparable F E] [FiniteDimensional E V]
    (h : HermitianForm F E V) {x y : V} (hxy : h.toSesq x x = h.toSesq y y)
    (hx : h.toSesq x x ≠ 0) :
    ∃ g : V ≃ₗ[E] V, (∀ z z', h.toSesq (g z) (g z') = h.toSesq z z') ∧ g x = y := by
  by_cases hd : h.toSesq x x - h.toSesq y x ≠ 0
  · exact h.exists_isometry_apply_eq_of_ne hxy hd
  push Not at hd
  obtain ⟨l, hl, hl1⟩ := exists_mul_conj_eq_one_ne_one (F := F) (E := E)
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl
  have hcl : conj F E l ≠ 1 := by
    intro h1; apply hl1; rw [← conj_conj (F := F) l, h1, map_one]
  have hxy' : h.toSesq x x = h.toSesq (l • y) (l • y) := by
    rw [h.toSesq_smul_left, h.toSesq_smul_right, ← hxy, ← mul_assoc, mul_comm (conj F E l), hl,
      one_mul]
  have hd' : h.toSesq x x - h.toSesq (l • y) x ≠ 0 := by
    rw [h.toSesq_smul_left, ← sub_eq_zero.1 hd]
    have : h.toSesq x x - conj F E l * h.toSesq x x = (1 - conj F E l) * h.toSesq x x := by ring
    rw [this]
    exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hcl)) hx
  obtain ⟨g, hg, hgx⟩ := h.exists_isometry_apply_eq_of_ne hxy' hd'
  refine ⟨g.trans (LinearEquiv.smulOfNeZero E V l⁻¹ (inv_ne_zero hl0)), fun z z' => ?_, ?_⟩
  · simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, h.toSesq_smul_left,
      h.toSesq_smul_right, hg, map_inv₀]
    rw [← mul_assoc, ← mul_inv, mul_comm (conj F E l), hl, inv_one, one_mul]
  · simp only [LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply, hgx, smul_smul,
      inv_mul_cancel₀ hl0, one_smul]
end GroundTheory.Automorphic.HermitianForm
