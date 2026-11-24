-- Prove2me | solution 1 for GlobalTheory.AffinePoints.continuous_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:15.807258+00:00
-- url     : https://prove2.me/submissions/55522b73-6483-4d42-920a-bb1e7f1dc68c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set
open MvPolynomial
variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] [TopologicalSpace C] {σ : Type*}
namespace GlobalTheory.AffinePoints
theorem _root_.solution (g : MvPolynomial σ R →ₐ[R] A) :
    Continuous (coords g : (A →ₐ[R] C) → σ → C) :=
  continuous_pi fun _ => continuous_eval _
end GlobalTheory.AffinePoints
