-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.adjointEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:08:48.270606+00:00
-- url     : https://prove2.me/submissions/ef0f231c-428f-4290-884c-e1e552bcad7a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_eq_adjointEquiv_iff

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
theorem _root_.solution (a b : V ≃ₗ[E] V) :
    h.adjointEquiv (a * b) = h.adjointEquiv b * h.adjointEquiv a := by
  symm
  rw [eq_adjointEquiv_iff]
  intro y x
  rw [LinearEquiv.mul_apply, toSesq_adjointEquiv_left, toSesq_adjointEquiv_left,
    LinearEquiv.mul_apply]
end GroundTheory.Automorphic.HermitianForm
