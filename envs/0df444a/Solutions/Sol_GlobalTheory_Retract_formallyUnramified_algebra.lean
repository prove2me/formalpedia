-- Prove2me | solution 1 for GlobalTheory.Retract.formallyUnramified_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:37.871323+00:00
-- url     : https://prove2.me/submissions/afcd28c0-a0bf-4536-a22f-568bc579aea6

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
theorem _root_.solution [Algebra.FormallyUnramified R B] :
    Algebra.FormallyUnramified R A :=
  Algebra.FormallyUnramified.of_surjective p (algHom_surjective s p h)
end GlobalTheory.Retract
