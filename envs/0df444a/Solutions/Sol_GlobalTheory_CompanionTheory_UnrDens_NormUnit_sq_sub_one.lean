-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.sq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:02.652727+00:00
-- url     : https://prove2.me/submissions/de283ed5-6ad9-4f6a-b106-889bb43eae56

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution (hq : 1 < q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h2 : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
  rw [h2, Nat.add_sub_cancel, Nat.add_sub_cancel]
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
