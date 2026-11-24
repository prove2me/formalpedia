-- Prove2me | solution 1 for GlobalTheory.choiceCount_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:49.22736+00:00
-- url     : https://prove2.me/submissions/735f77e6-3aa2-491c-ad95-27aa6af4237a

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
import Theorems.Thm_GlobalTheory_card_mem_BB_fixed_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (hB : Formalism.CyclotomicNorms.BBCount) (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) :
    Formalism.CyclotomicNorms.ChoiceCount := by
  intro Y N g₁ hY hN hg₁ hg₁' S hS
  classical
  have h2 : 2 ≤ g₁ := by
    have : (2 : ℝ) ≤ g₁ := by linarith
    exact_mod_cast this
  obtain ⟨hfin, hcard⟩ := (hB g₁ h2).2 N
  have hsub : S ⊆ hfin.toFinset.biUnion (fun ℓ => S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)) := by
    intro g hg
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := (hS g hg).2.2
    exact Finset.mem_biUnion.2 ⟨ℓ, hfin.mem_toFinset.2 hℓ2, Finset.mem_filter.2 ⟨hg, hℓ1⟩⟩
  have hbound : ∀ ℓ ∈ hfin.toFinset, ((S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)).card : ℝ) ≤
      1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := fun ℓ _ =>
    card_mem_BB_fixed_le hR Y hY ℓ N _ (fun g hg => ⟨(hS g (Finset.mem_filter.1 hg).1).1,
      (hS g (Finset.mem_filter.1 hg).1).2.1, (Finset.mem_filter.1 hg).2⟩)
  have hFc : (hfin.toFinset.card : ℝ) ≤ 3 * N + 1 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast hcard
  have hc : (S.card : ℝ) ≤
      ∑ ℓ ∈ hfin.toFinset, ((S.filter (fun g => ℓ ∈ Formalism.CyclotomicNorms.BB N g)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  calc (S.card : ℝ) ≤ _ := hc
    _ ≤ ∑ ℓ ∈ hfin.toFinset, (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) :=
        Finset.sum_le_sum hbound
    _ = hfin.toFinset.card * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * N + 1) * (1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) :=
        mul_le_mul_of_nonneg_right hFc
          (add_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith)))
end GlobalTheory
