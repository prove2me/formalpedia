-- Prove2me | solution 1 for GlobalTheory.Retract.smooth_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:16.349027+00:00
-- url     : https://prove2.me/submissions/a8c24485-af81-415d-a6c2-ae5f0543ac6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_finitePresentation_algebra
import Theorems.Thm_GlobalTheory_Retract_formallySmooth_algebra

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
theorem _root_.solution [Algebra.Smooth R B] : Algebra.Smooth R A :=
  ⟨formallySmooth_algebra s p h, finitePresentation_algebra s p h⟩
end GlobalTheory.Retract
