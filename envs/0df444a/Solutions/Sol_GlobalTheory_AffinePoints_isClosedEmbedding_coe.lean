-- Prove2me | solution 1 for GlobalTheory.AffinePoints.isClosedEmbedding_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:37.839801+00:00
-- url     : https://prove2.me/submissions/da44ec14-112c-45af-ad9d-254ff5f5f928

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
theorem _root_.solution [T2Space C] [IsTopologicalSemiring C] :
    IsClosedEmbedding (fun p : A →ₐ[R] C => (p : A → C)) := by
  refine ⟨isEmbedding_coe, ?_⟩
  have : range (fun p : A →ₐ[R] C => (p : A → C)) =
      {u | u 1 = 1} ∩ {u | u 0 = 0} ∩ (⋂ a, ⋂ b, {u | u (a * b) = u a * u b}) ∩
        (⋂ a, ⋂ b, {u | u (a + b) = u a + u b}) ∩
        ⋂ r, {u | u (algebraMap R A r) = algebraMap R C r} := by
    ext u
    simp only [mem_range, mem_inter_iff, mem_setOf_eq, mem_iInter]
    constructor
    · rintro ⟨p, rfl⟩; simp
    · rintro ⟨⟨⟨⟨h1, h0⟩, hm⟩, ha⟩, hr⟩
      exact ⟨⟨⟨⟨⟨u, h1⟩, hm⟩, h0, ha⟩, hr⟩, rfl⟩
  rw [this]
  refine ((((isClosed_eq ?_ ?_).inter (isClosed_eq ?_ ?_)).inter (isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_eq ?_ ?_)).inter (isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_eq ?_ ?_)).inter (isClosed_iInter fun r => isClosed_eq ?_ ?_)
  all_goals fun_prop
end GlobalTheory.AffinePoints
