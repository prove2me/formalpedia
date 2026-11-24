-- Prove2me | solution 1 for GlobalTheory.AffinePoints.continuousOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:37.830558+00:00
-- url     : https://prove2.me/submissions/2e4b2347-fd0f-4603-9786-0d06c319241c

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
theorem _root_.solution {X : Type*} [TopologicalSpace X] {f : X → (A →ₐ[R] C)} {s : Set X} :
    ContinuousOn f s ↔ ∀ a, ContinuousOn (fun x => f x a) s := by
  rw [isEmbedding_coe.continuousOn_iff, continuousOn_pi]; rfl
end GlobalTheory.AffinePoints
