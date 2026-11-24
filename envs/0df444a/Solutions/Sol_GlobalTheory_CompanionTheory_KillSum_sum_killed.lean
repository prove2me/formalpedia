-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KillSum.sum_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:14:08.283673+00:00
-- url     : https://prove2.me/submissions/1268b588-7039-4e22-bafd-8c0bd6a94ffc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilator
import Theorems.Thm_GlobalTheory_CompanionTheory_KillSum_add_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KillSum
namespace GlobalTheory.CompanionTheory.KillSum
theorem _root_.solution {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ) :
    ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨{0}, by simp, fun R _ _ h _ => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨l0, hc, hk⟩ := ih
    refine ⟨l0.bind fun b => (l τ).map fun a => a + b, ?_, ?_⟩
    · rw [Finset.prod_insert hτ, ← hc]
      simp [Multiset.card_bind, mul_comm]
    · intro R _ _ h hh
      rw [Finset.sum_insert hτ]
      exact add_killed _ _ _ _ (hh τ (Finset.mem_insert_self _ _))
        (hk R h fun t ht => hh t (Finset.mem_insert_of_mem ht))
end GlobalTheory.CompanionTheory.KillSum
