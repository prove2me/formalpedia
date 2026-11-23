-- Prove2me | solution 1 for GlobalTheory.AffinePoints.apply_eq_div_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:23.658994+00:00
-- url     : https://prove2.me/submissions/437d7b41-8c4a-489a-b380-988bf4061eaa

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
variable {R A B K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B] [Field K] [Algebra R K]
namespace GlobalTheory.AffinePoints
theorem _root_.solution (q : B →ₐ[R] K) {b : B} {a s : A} (hs : IsUnit (algebraMap A B s))
    (h : b * algebraMap A B s = algebraMap A B a) :
    q b = q (algebraMap A B a) / q (algebraMap A B s) := by
  rw [eq_div_iff (hs.map q).ne_zero, ← map_mul, h]
end GlobalTheory.AffinePoints
