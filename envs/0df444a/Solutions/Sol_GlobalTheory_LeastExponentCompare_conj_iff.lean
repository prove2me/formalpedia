-- Prove2me | solution 1 for GlobalTheory.LeastExponentCompare.conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:28.962073+00:00
-- url     : https://prove2.me/submissions/a4aa36ab-8e10-4f29-a070-f9be16467e88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_BalancedHermitianSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPositiveAdd
import Theorems.Thm_GlobalTheory_LeastExponentCompare_isCMField_of_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
set_option autoImplicit false
open NumberField NumberField.IsCMField TensorProduct
namespace GlobalTheory.LeastExponentCompare
namespace _root_.GlobalTheory.LeastExponentCompare
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by
  constructor
  · rintro ⟨h, hne⟩
    haveI := _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj E cj h hne
    refine ⟨this, funext fun z => ?_⟩
    let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
    exact φ₀.injective (by rw [h, complexEmbedding_complexConj, RCLike.star_def])
  · rintro ⟨_, rfl⟩
    refine ⟨fun φ z => by rw [complexEmbedding_complexConj, RCLike.star_def], ?_⟩
    by_contra hall
    push_neg at hall
    exact complexConj_ne_one E (AlgEquiv.ext hall)
end _root_.GlobalTheory.LeastExponentCompare
end GlobalTheory.LeastExponentCompare
