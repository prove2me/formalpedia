-- Prove2me | solution 1 for GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:31.243513+00:00
-- url     : https://prove2.me/submissions/632673be-31ee-4b28-b563-4b7c0e353fc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIndependentModPrimeOfPowLeCard
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIndependentModPrimeOfPowLeCardStatement
import Theorems.Thm_GlobalTheory_ph_a_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ) (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card → (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') → ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  first | exact @GlobalTheory.ph_a_basis | exact GlobalTheory.ph_a_basis | (intros; apply GlobalTheory.ph_a_basis <;> assumption)
end _root_.GlobalTheory.T
