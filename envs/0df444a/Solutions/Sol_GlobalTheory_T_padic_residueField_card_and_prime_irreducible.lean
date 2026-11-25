-- Prove2me | solution 1 for GlobalTheory.T.padic_residueField_card_and_prime_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:01.326331+00:00
-- url     : https://prove2.me/submissions/b0d56c05-6793-4244-9fb0-a21e1982d317

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducible
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducibleStatement
import Theorems.Thm_GlobalTheory_TAdicInt_card_residueField_and_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := by
  first | exact @GlobalTheory.TAdicInt.card_residueField_and_irreducible | exact GlobalTheory.TAdicInt.card_residueField_and_irreducible | (intros; apply GlobalTheory.TAdicInt.card_residueField_and_irreducible <;> assumption)
end _root_.GlobalTheory.T
