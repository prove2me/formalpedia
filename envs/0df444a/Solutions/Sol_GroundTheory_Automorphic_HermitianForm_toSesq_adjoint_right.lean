-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.toSesq_adjoint_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:42.188092+00:00
-- url     : https://prove2.me/submissions/99df28ea-b072-409e-b258-d89e4f3a5168

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus

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
theorem _root_.solution (A : Module.End E V) (x y : V) :
    h.toSesq x (h.adjoint A y) = h.toSesq (A x) y := by
  rw [← h.conj_toSesq, toSesq_adjoint_left, h.conj_toSesq]
end GroundTheory.Automorphic.HermitianForm
