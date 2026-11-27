-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.mem_torusF_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:40.673722+00:00
-- url     : https://prove2.me/submissions/c1900af9-cbd1-472a-a179-885ca85c8872

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup_iff_adjointEquiv_mul
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
theorem _root_.solution (t : TorusE (γ : V ≃ₗ[E] V)) :
    t ∈ h.torusF γ ↔ t.val ∈ h.unitaryGroup := by
  rw [torusF, MonoidHom.mem_ker, torusNorm_apply, mem_unitaryGroup_iff_adjointEquiv_mul]
  constructor
  · intro ht; simpa using congrArg TorusE.val ht
  · intro ht; exact TorusE.ext (by simpa using ht)
end GroundTheory.Automorphic.HermitianForm
