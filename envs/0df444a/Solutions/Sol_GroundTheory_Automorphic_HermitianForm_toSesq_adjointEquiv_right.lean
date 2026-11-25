-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.toSesq_adjointEquiv_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:31.259207+00:00
-- url     : https://prove2.me/submissions/8d9dfb87-8812-4f1f-9bc4-7feb7fb846cb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_adjoint_right

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
theorem _root_.solution (g : V ≃ₗ[E] V) (x y : V) :
    h.toSesq x (h.adjointEquiv g y) = h.toSesq (g x) y :=
  h.toSesq_adjoint_right _ x y
end GroundTheory.Automorphic.HermitianForm
