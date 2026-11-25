-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.eq_adjointEquiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:54.438907+00:00
-- url     : https://prove2.me/submissions/f35c1828-46f7-46aa-9050-549a562a0744

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
theorem _root_.solution (g b : V ≃ₗ[E] V) :
    b = h.adjointEquiv g ↔ ∀ y x, h.toSesq (b y) x = h.toSesq y (g x) := by
  refine ⟨fun hb y x => hb ▸ h.toSesq_adjointEquiv_left g y x, fun hb => ?_⟩
  apply LinearEquiv.ext fun y => ?_
  apply h.nonsingular.1
  ext x
  rw [hb, toSesq_adjointEquiv_left]
end GroundTheory.Automorphic.HermitianForm
