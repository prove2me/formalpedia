-- Prove2me | solution 1 for GlobalTheory.AffinePoints.isOpen_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:38.515866+00:00
-- url     : https://prove2.me/submissions/f261a427-8e65-4b43-9e93-0fc2d7bca8a7

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
variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [Semiring C] [Algebra R C] [TopologicalSpace C]
namespace GlobalTheory.AffinePoints
theorem _root_.solution [T1Space C] (f : A) : IsOpen {p : A →ₐ[R] C | p f ≠ 0} :=
  (isClosed_zeroSet f).isOpen_compl
end GlobalTheory.AffinePoints
