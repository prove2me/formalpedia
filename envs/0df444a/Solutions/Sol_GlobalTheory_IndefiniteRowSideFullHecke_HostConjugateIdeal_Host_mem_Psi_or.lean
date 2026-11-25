-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host.mem_Psi_or
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:08.302083+00:00
-- url     : https://prove2.me/submissions/ac92d050-9294-4414-aa61-79803fbd3de1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
variable (H : Host E)
namespace GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
theorem _root_.solution (τ : E →+* ℂ) : τ ∈ H.Psi ∨ (starRingEnd ℂ).comp τ ∈ H.Psi := by
  have h : (τ H.s) ^ 2 = H.s₀ ^ 2 := by
    rw [← map_pow, H.s_sq, map_neg, map_natCast, H.s₀_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact Or.inl h
  · right
    change (starRingEnd ℂ) (τ H.s) = H.s₀
    rw [← IsCMField.complexEmbedding_complexConj, H.isCMField_complexConj_s_eq_neg, map_neg, h, neg_neg]
end GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Host
