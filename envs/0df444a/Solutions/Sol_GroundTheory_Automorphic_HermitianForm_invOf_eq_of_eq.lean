-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.invOf_eq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:53.505444+00:00
-- url     : https://prove2.me/submissions/48003c63-f31d-4764-ad0d-6599efc6b77d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_inv
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_mul
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_TorusE_ext
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_inv
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mk
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mul
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_one
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.TorusE.val_inv
attribute [local simp] GroundTheory.Automorphic.TorusE.val_mk
attribute [local simp] GroundTheory.Automorphic.TorusE.val_mul
attribute [local simp] GroundTheory.Automorphic.TorusE.val_one
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (g g' : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup)
    (hg' : g' * γ * g'⁻¹ ∈ h.unitaryGroup) (heq : g * γ * g⁻¹ = g' * γ * g'⁻¹) :
    h.invOf γ g hg = h.invOf γ g' hg' := by
  have htE : g⁻¹ * g' ∈ torusE (γ : V ≃ₗ[E] V) := by
    rw [mem_torusE]
    calc (γ : V ≃ₗ[E] V) * (g⁻¹ * g') = g⁻¹ * (g * γ * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * γ * g'⁻¹) * g' := by rw [heq]
      _ = g⁻¹ * g' * γ := by group
  set t := TorusE.mk _ htE
  rw [invOf, invOf, mk_eq_mk_iff]
  refine ⟨t, ?_⟩
  have hc : (h.normOf γ g hg : TorusE (γ : V ≃ₗ[E] V)) * h.torusNorm γ t =
      h.torusStar γ t * h.normOf γ g hg * t := by
    rw [torusNorm_apply]
    simp only [mul_comm, mul_left_comm]
  rw [hc]
  apply TorusE.ext
  simp only [TorusE.val_mul, val_torusStar, val_normOf, t, TorusE.val_mk, adjointEquiv_mul,
    adjointEquiv_inv]
  group
end GroundTheory.Automorphic.HermitianForm
