-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.stableInv_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:47.872069+00:00
-- url     : https://prove2.me/submissions/ce875dc6-f4a6-4b73-abad-2af1a447a017

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_stableInv_conj
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_one
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
theorem _root_.solution : h.stableInv γ γ = 1 := by
  have hg : (1 : V ≃ₗ[E] V) * γ * 1⁻¹ ∈ h.unitaryGroup := by simp
  have := h.stableInv_conj γ 1 hg
  simp only [one_mul, inv_one, mul_one] at this
  have h1 : h.normOf γ 1 hg = 1 := Subtype.ext (TorusE.ext (by simp [adjointEquiv_one]))
  rw [this, invOf, h1, QuotientGroup.mk_one]
end GroundTheory.Automorphic.HermitianForm
