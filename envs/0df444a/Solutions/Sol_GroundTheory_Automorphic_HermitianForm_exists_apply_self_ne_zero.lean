-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_apply_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:27.809358+00:00
-- url     : https://prove2.me/submissions/addeaf2b-e6b9-41bd-808f-d99689669a10

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Theorems.Thm_GroundTheory_Automorphic_exists_trace_eq_one
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_eq_zero_of_forall
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_add_conj
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj


attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
open GroundTheory.Automorphic.HermitianForm
variable [Algebra.IsSeparable F E]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) [Nontrivial V] :
    ∃ x, h.toSesq x x ≠ 0 := by
  by_contra H
  push Not at H
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ : ∃ y, h.toSesq x y ≠ 0 := by
    by_contra H'
    push Not at H'
    exact hx (h.eq_zero_of_forall H')
  obtain ⟨c, hc⟩ := exists_trace_eq_one (F := F) (E := E)
  set t := c * (h.toSesq x y)⁻¹ with ht_def
  have ht : t * h.toSesq x y = c := by rw [ht_def]; field_simp
  have key : h.toSesq (x + t • y) (x + t • y) =
      t * h.toSesq x y + conj F E (t * h.toSesq x y) := by
    rw [map_mul, h.conj_toSesq]
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, H]
    ring
  rw [H, ht, add_conj, hc, map_one] at key
  exact one_ne_zero key.symm
end GroundTheory.Automorphic.HermitianForm
