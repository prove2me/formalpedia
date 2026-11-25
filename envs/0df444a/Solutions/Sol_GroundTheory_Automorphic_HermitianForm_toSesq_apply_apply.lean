-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.toSesq_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:51.444466+00:00
-- url     : https://prove2.me/submissions/e59e3957-6340-47bc-95e1-9df65ba3493f

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
theorem _root_.solution (g : V ≃ₗ[E] V) (x y : V) :
    h.toSesq (g x) (g y) = h.toSesq ((h.adjointEquiv g * g) x) y := by
  rw [LinearEquiv.mul_apply, toSesq_adjointEquiv_left]
end GroundTheory.Automorphic.HermitianForm
