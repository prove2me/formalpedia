-- Prove2me | solution 1 for GlobalTheory.RandomTops.tail_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:43.672113+00:00
-- url     : https://prove2.me/submissions/5ce06b45-56bd-40e5-804c-c4171bc16e25

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_pos
import Theorems.Thm_GlobalTheory_RandomTops_ind_nonneg
import Theorems.Thm_GlobalTheory_RandomTops_ind_le
import Theorems.Thm_GlobalTheory_RandomTops_ex_sum
import Theorems.Thm_GlobalTheory_RandomTops_ex_mono
import Theorems.Thm_GlobalTheory_RandomTops_ex_contains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {B : Finset ℕ} {L : ℕ} (hB : B.card ≤ L) (K : ℕ) :
    ex δ B (fun T => ind (K ≤ T.card)) ≤ (L.choose K : ℝ) * δ ^ K := by
  have hpt : ∀ T ⊆ B, ind (K ≤ #T) ≤ ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T) := by
    intro T hT
    refine ind_le (sum_nonneg fun _ _ => ind_nonneg _) fun hK => ?_
    obtain ⟨Q, hQT, hQ⟩ := Finset.exists_subset_card_eq hK
    have hQB : Q ∈ B.powersetCard K := mem_powersetCard.mpr ⟨hQT.trans hT, hQ⟩
    calc (1 : ℝ) = ind (Q ⊆ T) := (ind_pos hQT).symm
      _ ≤ _ := single_le_sum (f := fun Q => ind (Q ⊆ T)) (fun _ _ => ind_nonneg _) hQB
  calc ex δ B (fun T => ind (K ≤ #T))
      ≤ ex δ B (fun T => ∑ Q ∈ B.powersetCard K, ind (Q ⊆ T)) := ex_mono h0 h1 hpt
    _ = ∑ Q ∈ B.powersetCard K, ex δ B (fun T => ind (Q ⊆ T)) :=
      ex_sum _ _ (fun Q T => ind (Q ⊆ T))
    _ = ∑ Q ∈ B.powersetCard K, δ ^ K := sum_congr rfl fun Q hQ => by
      rw [ex_contains (mem_powersetCard.mp hQ).1, (mem_powersetCard.mp hQ).2]
    _ = ((#B).choose K : ℝ) * δ ^ K := by rw [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (L.choose K : ℝ) * δ ^ K :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose K hB) (pow_nonneg h0 _)
end GlobalTheory.RandomTops
