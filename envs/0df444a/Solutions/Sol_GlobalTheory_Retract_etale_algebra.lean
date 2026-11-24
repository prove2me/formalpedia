-- Prove2me | solution 1 for GlobalTheory.Retract.etale_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:15.496513+00:00
-- url     : https://prove2.me/submissions/9adee337-0acb-4054-8eac-d8ec9d1dd763

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_finitePresentation_algebra
import Theorems.Thm_GlobalTheory_Retract_formallyEtale_algebra

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
theorem _root_.solution [Algebra.Etale R B] : Algebra.Etale R A :=
  ⟨formallyEtale_algebra s p h, finitePresentation_algebra s p h⟩
end GlobalTheory.Retract
