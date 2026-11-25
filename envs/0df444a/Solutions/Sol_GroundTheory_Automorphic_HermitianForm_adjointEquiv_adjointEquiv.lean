-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.adjointEquiv_adjointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:32:57.033978+00:00
-- url     : https://prove2.me/submissions/b3a1fc4d-5654-40d0-9403-8da89e0ce5ba

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_adjointEquiv_right
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
theorem _root_.solution (a : V ≃ₗ[E] V) : h.adjointEquiv (h.adjointEquiv a) = a := by
  symm
  rw [eq_adjointEquiv_iff]
  intro y x
  rw [toSesq_adjointEquiv_right]
end GroundTheory.Automorphic.HermitianForm
