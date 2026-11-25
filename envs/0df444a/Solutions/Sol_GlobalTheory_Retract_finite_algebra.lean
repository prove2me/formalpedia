-- Prove2me | solution 1 for GlobalTheory.Retract.finite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:49.494259+00:00
-- url     : https://prove2.me/submissions/09a1b892-4214-4eee-a719-27516e0a0981

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_algHom_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (s : A →ₐ[R] B) (p : B →ₐ[R] A) (h : p.comp s = AlgHom.id R A)
include h
namespace GlobalTheory.Retract
theorem _root_.solution [Module.Finite R B] : Module.Finite R A :=
  Module.Finite.of_surjective p.toLinearMap (algHom_surjective s p h)
end GlobalTheory.Retract
