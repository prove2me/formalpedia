-- Prove2me | solution 1 for GlobalTheory.Retract.quasiFinite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:35.505625+00:00
-- url     : https://prove2.me/submissions/0bc8dcc6-d652-4501-bb21-b5c75d89e9df

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
theorem _root_.solution [Algebra.QuasiFinite R B] : Algebra.QuasiFinite R A :=
  Algebra.QuasiFinite.of_surjective_algHom p (algHom_surjective s p h)
end GlobalTheory.Retract
