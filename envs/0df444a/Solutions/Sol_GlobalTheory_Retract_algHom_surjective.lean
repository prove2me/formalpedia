-- Prove2me | solution 1 for GlobalTheory.Retract.algHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:59.426167+00:00
-- url     : https://prove2.me/submissions/e86d716e-c039-4e38-a4e3-eb1a68ffdeec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation

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
theorem _root_.solution : Function.Surjective p :=
  fun a ↦ ⟨s a, congr($h a)⟩
end GlobalTheory.Retract
