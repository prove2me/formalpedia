-- Prove2me | solution 1 for GlobalTheory.AffinePoints.aeval_coords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:29.209059+00:00
-- url     : https://prove2.me/submissions/a477731c-0f29-4ba0-923f-7e2b64dd2b2a

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
omit [TopologicalSpace C]
namespace GlobalTheory.AffinePoints
theorem _root_.solution (g : MvPolynomial σ R →ₐ[R] A) (p : A →ₐ[R] C) (q : MvPolynomial σ R) :
    aeval (coords g p) q = p (g q) := by
  have : (aeval (coords g p) : MvPolynomial σ R →ₐ[R] C) = p.comp g := by ext i; simp
  rw [this]; rfl
end GlobalTheory.AffinePoints
