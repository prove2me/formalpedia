-- Prove2me | solution 1 for GlobalTheory.Retract.finitePresentation_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:51.099234+00:00
-- url     : https://prove2.me/submissions/c8b34381-9b52-49be-97b9-5f069341be52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_algHom_surjective
import Theorems.Thm_GlobalTheory_Retract_fg_ker

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
theorem _root_.solution [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A :=
  Algebra.FinitePresentation.of_surjective (algHom_surjective s p h) (fg_ker s p h)
end GlobalTheory.Retract
