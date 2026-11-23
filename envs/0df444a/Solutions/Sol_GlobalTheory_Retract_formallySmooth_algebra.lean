-- Prove2me | solution 1 for GlobalTheory.Retract.formallySmooth_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:12.037844+00:00
-- url     : https://prove2.me/submissions/bcb75334-707b-4228-b4d5-e690684e0b90

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
theorem _root_.solution [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by
  refine Algebra.FormallySmooth.of_split p
    ((Ideal.Quotient.mkₐ R (RingHom.ker p.toRingHom ^ 2)).comp s) ?_
  ext a
  exact congr($h a)
end GlobalTheory.Retract
