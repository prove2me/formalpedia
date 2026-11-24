-- Prove2me | solution 1 for GlobalTheory.Retract.formallyEtale_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:34.659133+00:00
-- url     : https://prove2.me/submissions/81b0481d-4b6d-43a3-b574-26be67760db4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_formallySmooth_algebra
import Theorems.Thm_GlobalTheory_Retract_formallyUnramified_algebra

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
theorem _root_.solution [Algebra.FormallyEtale R B] : Algebra.FormallyEtale R A :=
  Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨formallyUnramified_algebra s p h, formallySmooth_algebra s p h⟩
end GlobalTheory.Retract
