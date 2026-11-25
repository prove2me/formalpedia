-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isOrthoCompl_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:28.924794+00:00
-- url     : https://prove2.me/submissions/200f3e91-bb20-4565-a909-661de0df0303

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
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
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) {v : V}
    (hv : h.toSesq v v ≠ 0) :
    h.IsOrthoCompl (Submodule.span E {v}) (LinearMap.ker (h.toSesq v)) := by
  refine ⟨?_, ?_⟩
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor
    · rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx1
      have : t * h.toSesq v v = 0 := by
        simpa [LinearMap.mem_ker, h.toSesq_smul_right] using hx2
      rcases mul_eq_zero.1 this with ht | ht
      · simp [ht]
      · exact absurd ht hv
    · rw [eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      refine ⟨(h.toSesq v x * (h.toSesq v v)⁻¹) • v, Submodule.mem_span_singleton.2 ⟨_, rfl⟩,
        x - (h.toSesq v x * (h.toSesq v v)⁻¹) • v, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, h.toSesq_smul_right]
      field_simp
      ring
  · intro x hx y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.mem_ker] at hy
    rw [h.toSesq_smul_left, hy, mul_zero]
end GroundTheory.Automorphic.HermitianForm
