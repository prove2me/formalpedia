-- Prove2me | solution 1 for GlobalTheory.RandomTops.prob_not_good_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:27.444928+00:00
-- url     : https://prove2.me/submissions/9bc91d90-e252-434b-80d4-289d4ccb49bc

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_pos
import Theorems.Thm_GlobalTheory_RandomTops_ind_nonneg
import Theorems.Thm_GlobalTheory_RandomTops_ind_le
import Theorems.Thm_GlobalTheory_RandomTops_ex_add
import Theorems.Thm_GlobalTheory_RandomTops_ex_mono
import Theorems.Thm_GlobalTheory_RandomTops_condProbAt_eq
import Theorems.Thm_GlobalTheory_RandomTops_tail_le_choose
import Theorems.Thm_GlobalTheory_RandomTops_tail_le_binUpper
import Theorems.Thm_GlobalTheory_RandomTops_windows_le
import Theorems.Thm_GlobalTheory_RandomTops_tiles_le

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
theorem _root_.solution : Formalism.G0.TileConditionFailureProbBound := by
  intro n δ L₂ K r u M₀ G' N₁ i₀ h0 h1 _ hu hn hi
  rw [condProbAt_eq hi]
  have hpt : ∀ U ⊆ (range n).erase i₀, ind (¬ GoodOrbitIntervalTileCondition n (insert i₀ U) L₂ K r u M₀ G' N₁) ≤
      ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K) +
        ind (¬ CondTiles n (insert i₀ U) r u M₀) +
        ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁) := by
    intro U _
    have ha := ind_nonneg (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K)
    have hb := ind_nonneg (¬ CondTiles n (insert i₀ U) r u M₀)
    have hc := ind_nonneg (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁)
    refine ind_le (by linarith) fun hng => ?_
    by_cases hA : ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K
    · by_cases hB : CondTiles n (insert i₀ U) r u M₀
      · have hC : ¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁ := fun hC => hng ⟨hA, hB, hC⟩
        rw [ind_pos hC]
        linarith
      · rw [ind_pos hB]
        linarith
    · rw [ind_pos hA]
      linarith
  have ha := windows_le h0 h1 n i₀ L₂ K K le_rfl ((L₂.choose K : ℝ) * δ ^ K)
    (fun A hA => tail_le_choose h0 h1 hA K)
  have hb := tiles_le (i₀ := i₀) h0 h1 hu hn
  have hc := windows_le h0 h1 n i₀ G' N₁ (N₁ - 1) (Nat.sub_le _ _) (binUpper G' δ (N₁ - 1))
    (fun A hA => tail_le_binUpper h0 h1 hA (N₁ - 1))
  calc _ ≤ ex δ ((range n).erase i₀) (fun U =>
        ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K) +
          ind (¬ CondTiles n (insert i₀ U) r u M₀) +
          ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁)) := ex_mono h0 h1 hpt
    _ = ex δ ((range n).erase i₀) (fun U => ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i L₂) ≤ K)) +
        ex δ ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) +
        ex δ ((range n).erase i₀) (fun U => ind (¬ ∀ i < n, #(insert i₀ U ∩ window n i G') ≤ N₁)) := by
      rw [ex_add, ex_add]
    _ ≤ _ := by linarith
end GlobalTheory.RandomTops
