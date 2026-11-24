-- Prove2me | solution 1 for GlobalTheory.idempotent_eq_of_sub_mem_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:28.599982+00:00
-- url     : https://prove2.me/submissions/11fd1080-ea44-4c66-8c77-390aac912a6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (h : a - b ∈ (⊥ : Ideal S).jacobson) :
    a = b := by
  have hu : IsUnit ((a - b) * (-(a - b)) + 1) := Ideal.mem_jacobson_bot.1 h _
  have h0 : ((a - b) * (-(a - b)) + 1) * (a - b) = 0 := by
    have h1 := ha.eq
    have h2 := hb.eq
    linear_combination (-a - 1 + 3 * b) * h1 + (b + 1 - 3 * a) * h2
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)
end GlobalTheory
