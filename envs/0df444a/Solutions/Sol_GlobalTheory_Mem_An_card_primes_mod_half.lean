-- Prove2me | solution 1 for GlobalTheory.Mem.An.card_primes_mod_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:24.361455+00:00
-- url     : https://prove2.me/submissions/618b1f06-72a2-497c-9d83-ff47d6a2522b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimesAPIntervalOfTzRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
namespace GlobalTheory.Mem.An
theorem _root_.solution (n a N : ℕ) (hn : Odd n) (ha : Nat.Coprime a (2 * n)) :
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ∧
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card + 1 := by
  constructor
  · apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.of_mul_left 2⟩
  · refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le 2 _)
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_insert, Finset.mem_filter]
    by_cases h2 : p = 2
    · exact Or.inl h2
    · right
      refine ⟨hp.1, hp.2.1, ?_⟩
      have hc : Nat.Coprime 2 n := (Nat.coprime_two_left).2 hn
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hc]
      refine ⟨?_, hp.2.2⟩
      have hpo : Odd p := hp.2.1.odd_of_ne_two h2
      have hao : Odd a := (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right ha)
      unfold Nat.ModEq
      rw [Nat.odd_iff.1 hpo, Nat.odd_iff.1 hao]
end GlobalTheory.Mem.An
