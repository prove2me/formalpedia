-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_isotropic_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:28.176495+00:00
-- url     : https://prove2.me/submissions/4d0c95ef-861b-4b74-9903-815df3360625

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_self_mem_range
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_add_conj
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_exists_trace_eq_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) (U : Submodule E V) {r : V}
    (hrU : r ∈ U) (hr : ∀ u ∈ U, h.toSesq r u = 0) (μ : U →ₗ[E] E) (hμ : μ ⟨r, hrU⟩ = 1) :
    ∃ s : V, (∀ u : U, h.toSesq s u = μ u) ∧ h.toSesq s s = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend μ
  obtain ⟨s₀, hs₀⟩ := h.nonsingular.2 g
  have hs₀u : ∀ u : U, h.toSesq s₀ u = μ u := fun u => by
    rw [hs₀, ← hg]
    rfl
  obtain ⟨e₀, he₀⟩ := h.toSesq_self_mem_range s₀
  obtain ⟨c, hc⟩ := exists_trace_eq_one (F := F) (E := E)
  have hc1 : c + conj F E c = 1 := by rw [add_conj, hc, map_one]
  refine ⟨s₀ + (-(c * algebraMap F E e₀)) • r, fun u => ?_, ?_⟩
  · rw [map_add, LinearMap.add_apply, h.toSesq_smul_left, hr u u.2, mul_zero, add_zero, hs₀u]
  · have h1 : h.toSesq s₀ r = 1 := by rw [← hμ, ← hs₀u]
    have h2 : h.toSesq r s₀ = 1 := by rw [← h.conj_toSesq, h1, map_one]
    have h3 : h.toSesq r r = 0 := hr r hrU
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, h1, h2, h3]
    rw [← he₀, map_neg, map_mul, conj_algebraMap]
    linear_combination (-(algebraMap F E e₀)) * hc1
end GroundTheory.Automorphic.HermitianForm
