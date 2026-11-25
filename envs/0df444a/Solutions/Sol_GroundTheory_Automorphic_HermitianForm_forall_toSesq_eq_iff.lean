-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.forall_toSesq_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:09:28.029995+00:00
-- url     : https://prove2.me/submissions/7fe10896-af4a-48e6-9386-b26c22eaf1cf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_apply_apply

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
theorem _root_.solution (g c : V ≃ₗ[E] V) :
    (∀ x y, h.toSesq (g x) (g y) = h.toSesq (c x) y) ↔ h.adjointEquiv g * g = c := by
  constructor
  · intro hg
    apply LinearEquiv.ext fun x => h.nonsingular.1 (LinearMap.ext fun y => ?_)
    rw [← toSesq_apply_apply, hg]
  · intro hg x y
    rw [toSesq_apply_apply, hg]
end GroundTheory.Automorphic.HermitianForm
