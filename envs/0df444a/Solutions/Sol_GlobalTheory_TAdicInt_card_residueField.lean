-- Prove2me | solution 1 for GlobalTheory.TAdicInt.card_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:22.399181+00:00
-- url     : https://prove2.me/submissions/64763259-4668-4815-88ab-3fde31d13844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducible

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
theorem _root_.solution (T : ℕ) [Fact T.Prime] : Nat.card (ResidueField 𝒪[ℚ_[T]]) = T := by
  rw [Nat.card_congr ((ResidueField.mapEquiv (intEquiv T)).trans PadicInt.residueField).toEquiv, Nat.card_zmod]
end GlobalTheory.TAdicInt
