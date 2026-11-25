-- Prove2me | solution 1 for GlobalTheory.TAdicInt.card_residueField_and_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:38:58.230891+00:00
-- url     : https://prove2.me/submissions/ca1011ad-6331-4e92-9fe7-b2b86125a869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducible
import Theorems.Thm_GlobalTheory_TAdicInt_card_residueField
import Theorems.Thm_GlobalTheory_TAdicInt_irreducible_natCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.TAdicInt
namespace GlobalTheory.TAdicInt
theorem _root_.solution :
    ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧
      Irreducible ((T : 𝒪[ℚ_[T]])) :=
  fun T _ => ⟨card_residueField T, irreducible_natCast T⟩
end GlobalTheory.TAdicInt
