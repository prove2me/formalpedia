-- Prove2me | solution 1 for GlobalTheory.T.exists_divided_powers_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:24.73027+00:00
-- url     : https://prove2.me/submissions/7ba06b9a-3977-49d1-a895-ea4c16696a66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrimeStatement
import Theorems.Thm_GlobalTheory_TorsionFreeDividedPowers_exists_dividedPowers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m := by
  first | exact @GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers | exact GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers | (intros; apply GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers <;> assumption)
end _root_.GlobalTheory.T
