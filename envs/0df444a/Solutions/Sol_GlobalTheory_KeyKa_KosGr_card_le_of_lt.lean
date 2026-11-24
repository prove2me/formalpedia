-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.card_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:27.325089+00:00
-- url     : https://prove2.me/submissions/77a10afe-9355-4d14-8273-e584bc4024da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution (I : Finset (Fin g)) (r : ℕ) (hI : ∀ k ∈ I, k.val < r) : I.card ≤ r := by
  calc I.card = (I.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range r).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_range.mpr (hI k hk)
    _ = r := Finset.card_range r
end GlobalTheory.KeyKa.KosGr
