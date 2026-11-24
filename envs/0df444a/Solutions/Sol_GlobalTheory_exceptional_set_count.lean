-- Prove2me | solution 1 for GlobalTheory.exceptional_set_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:45.372967+00:00
-- url     : https://prove2.me/submissions/411542b2-bd99-4ef5-ae9c-1d2b92a61f8f

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe
import Theorems.Thm_GlobalTheory_exceptional_primes_finite_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.CyclotomicNorms.BBCount := by
  intro g hg
  have key : ∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ∧
      Set.ncard {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ≤ 3 := by
    intro d hd
    have h1 : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    exact exceptional_primes_finite_card_le (g ^ d - 1) (g ^ d) (by omega) (by omega)
  refine ⟨key, fun N => ?_⟩
  induction N with
  | zero =>
    have : Formalism.CyclotomicNorms.BB 0 g = {g} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, -⟩)
        · exact h
        · omega
      · exact Or.inl
    rw [this]
    simp
  | succ N ih =>
    have : Formalism.CyclotomicNorms.BB (N + 1) g = Formalism.CyclotomicNorms.BB N g ∪ {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge N d with h | h
          · obtain rfl : d = N + 1 := by omega
            exact Or.inr h3
          · exact Or.inl (Or.inr ⟨d, h1, h, h3⟩)
      · rintro ((h | ⟨d, h1, h2, h3⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨d, h1, by omega, h3⟩
        · exact Or.inr ⟨N + 1, by omega, le_rfl, h⟩
    rw [this]
    obtain ⟨hf, hc⟩ := key (N + 1) (by omega)
    refine ⟨ih.1.union hf, ?_⟩
    have := Set.ncard_union_le (Formalism.CyclotomicNorms.BB N g) {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ}
    have := ih.2
    omega
end GlobalTheory
