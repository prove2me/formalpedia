-- Prove2me | solution 1 for GlobalTheory.MultinomialCount.cons_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:28.630868+00:00
-- url     : https://prove2.me/submissions/b4daa69e-ed69-4c42-9c43-58de6e4e6814

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorial
import Theorems.Thm_GlobalTheory_MultinomialCount_ofFn_cons_count

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open GlobalTheory GlobalTheory.MultinomialCount
namespace GlobalTheory.MultinomialCount
theorem _root_.solution {I : Type} {k : ℕ} (ν : I → ℕ) (a : I) (t : Fin k → I) :
    (∀ i, (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = ν i) ↔
      (1 ≤ ν a ∧ ∀ i, (List.ofFn t).count i = Function.update ν a (ν a - 1) i) := by
  simp only [ofFn_cons_count]
  constructor
  · intro h
    have ha := h a
    simp only [if_true] at ha
    refine ⟨by omega, fun i => ?_⟩
    by_cases hi : i = a
    · subst hi; simp only [Function.update_self]; omega
    · have := h i
      rw [if_neg (Ne.symm hi)] at this
      simp only [Function.update_apply, hi, if_false]; omega
  · rintro ⟨h1, h⟩ i
    by_cases hi : i = a
    · subst hi; have := h i; simp only [Function.update_self] at this; simp only [if_true]; omega
    · have := h i
      simp only [Function.update_apply, hi, if_false] at this
      rw [if_neg (Ne.symm hi)]; omega
end GlobalTheory.MultinomialCount
