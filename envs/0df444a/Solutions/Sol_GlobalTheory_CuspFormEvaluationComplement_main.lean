-- Prove2me | solution 1 for GlobalTheory.CuspFormEvaluationComplement.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:05:34.671811+00:00
-- url     : https://prove2.me/submissions/13bde8b8-5b3b-4329-b29f-de6f0aa8aa7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspFormEvaluationComplement
namespace GlobalTheory.CuspFormEvaluationComplement
theorem _root_.solution : ∀ (s : Multiset ℂ) {t : ℝ}, (0 : ℝ) ≤ t → (∀ μ ∈ s, ‖μ - (1 : ℂ)‖ ≤ t) →
    ‖Multiset.prod s - (1 : ℂ)‖ ≤ Real.exp ((↑(Multiset.card s) : ℝ) * t) - (1 : ℝ) := by
  intro s t ht hs
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ‖a - 1‖ ≤ t := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    rw [Multiset.prod_cons, Multiset.card_cons]
    have hna : ‖a‖ ≤ 1 + t := by
      have h0 : a = (a - 1) + 1 := by ring
      calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [← h0]
        _ ≤ ‖a - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + t := by rw [norm_one]; linarith
    have key : a * s.prod - 1 = a * (s.prod - 1) + (a - 1) := by ring
    have h1 : ‖a * s.prod - 1‖ ≤ (1 + t) * (Real.exp ((Multiset.card s : ℝ) * t) - 1) + t := by
      rw [key]
      calc ‖a * (s.prod - 1) + (a - 1)‖ ≤ ‖a * (s.prod - 1)‖ + ‖a - 1‖ := norm_add_le _ _
        _ = ‖a‖ * ‖s.prod - 1‖ + ‖a - 1‖ := by rw [norm_mul]
        _ ≤ (1 + t) * (Real.exp ((Multiset.card s : ℝ) * t) - 1) + t :=
          add_le_add (mul_le_mul hna ih' (norm_nonneg _) (by linarith)) ha
    have h2 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hE := Real.exp_pos ((Multiset.card s : ℝ) * t)
    have h3 := mul_le_mul_of_nonneg_right h2 hE.le
    have hexp : Real.exp (((Multiset.card s + 1 : ℕ) : ℝ) * t)
        = Real.exp t * Real.exp ((Multiset.card s : ℝ) * t) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [hexp]
    nlinarith [h1, h3]
end GlobalTheory.CuspFormEvaluationComplement
