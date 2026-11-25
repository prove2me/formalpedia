-- Prove2me | solution 1 for GlobalTheory.BadShare.samePart_roots_finite_ncard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:16.026574+00:00
-- url     : https://prove2.me/submissions/c27e48b2-6d9d-426a-88d2-64938e8bde70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
import Theorems.Thm_GlobalTheory_BadShare_primePowRoots_finite_ncard
import Theorems.Thm_GlobalTheory_BadShare_samePart_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution :
    ∀ (k : Type) [Field k] (n l : ℕ), 0 < n → l.Prime →
      ({y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
        {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n) ∧
      ∀ z : k, {x : k | x ^ n = 1 ∧ SamePart l x z}.Finite ∧
        {x : k | x ^ n = 1 ∧ SamePart l x z}.ncard ≤ l ^ padicValNat l n := by
  intro k _ n l hn hl
  obtain ⟨hf, hc⟩ := primePowRoots_finite_ncard k n l hn hl
  refine ⟨⟨hf, hc⟩, fun z => ?_⟩
  rcases Set.eq_empty_or_nonempty {x : k | x ^ n = 1 ∧ SamePart l x z} with he | ⟨x₀, hx₀, hb⟩
  · rw [he]; simp
  have hsub : {x : k | x ^ n = 1 ∧ SamePart l x z} ⊆
      (fun y => y * x₀) '' {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} := by
    rintro x ⟨hx, ha⟩
    have hs : SamePart l x x₀ := Eq.trans ha (Eq.symm hb)
    obtain ⟨a, ha⟩ := (samePart_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx⟩)
      (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx₀⟩)).1 hs
    have h0 : x₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hx₀
      exact zero_ne_one hx₀
    refine ⟨x / x₀, ⟨?_, a, ?_⟩, div_mul_cancel₀ x h0⟩
    · rw [div_pow, hx, hx₀, div_one]
    · rw [div_pow, ha, div_self (pow_ne_zero _ h0)]
  refine ⟨(hf.image _).subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans hc)
end GlobalTheory.BadShare
