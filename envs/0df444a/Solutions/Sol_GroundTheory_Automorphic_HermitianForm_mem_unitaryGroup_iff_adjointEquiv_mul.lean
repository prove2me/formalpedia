-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.mem_unitaryGroup_iff_adjointEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:27.402251+00:00
-- url     : https://prove2.me/submissions/395d50ec-d92a-48d0-a0db-e874a7e602c6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_apply_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔ h.adjointEquiv g * g = 1 := by
  rw [mem_unitaryGroup]
  constructor
  · intro hg
    apply LinearEquiv.ext fun x => h.nonsingular.1 (LinearMap.ext fun y => ?_)
    rw [← toSesq_apply_apply, hg]
    rfl
  · intro hg x y
    rw [toSesq_apply_apply, hg]
    rfl
end GroundTheory.Automorphic.HermitianForm
