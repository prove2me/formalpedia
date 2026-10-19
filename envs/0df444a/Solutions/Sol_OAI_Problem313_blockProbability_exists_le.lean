-- Prove2me | solution 1 for OAI.Problem313.blockProbability_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:07:37.533539+00:00
-- url     : https://prove2.me/submissions/27138fa7-5220-4f83-93fe-a9c8a5621896

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean:L138-L152
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.blockProbability_exists_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting

-- ---- from OAI.Combinatorics.SharpThreshold.BlockCounting ----
namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
theorem blockProbability_eq (U : Finset α) (m : ℕ) (P : Finset α → Prop)
    [DecidablePred P] : blockProbability U m P =
      (((U.powersetCard m).filter P).card : ℝ) / (U.powersetCard m).card := by
  unfold blockProbability
  congr

omit [DecidableEq α] in
theorem blockProbability_mono (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B → Q B) :
    blockProbability U m P ≤ blockProbability U m Q := by
  classical
  unfold blockProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (U.powersetCard m).filter P ⊆
      (U.powersetCard m).filter Q from by
    intro B hB
    obtain ⟨hB, hP⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨hB, hPQ B hB hP⟩)

omit [DecidableEq α] in
theorem blockProbability_congr (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B ↔ Q B) :
    blockProbability U m P = blockProbability U m Q := by
  apply le_antisymm
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mp)
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mpr)

theorem blockProbability_or_le (U : Finset α) (m : ℕ)
    (P Q : Finset α → Prop) :
    blockProbability U m (fun B => P B ∨ Q B) ≤
      blockProbability U m P + blockProbability U m Q := by
  classical
  simp only [blockProbability_eq, Finset.filter_or]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le ((U.powersetCard m).filter P)
    ((U.powersetCard m).filter Q)

theorem blockProbability_exists_le (U : Finset α) (m : ℕ)
    (V : Finset α) (P : α → Finset α → Prop) :
    blockProbability U m (fun B => ∃ v ∈ V, P v B) ≤
      ∑ v ∈ V, blockProbability U m (P v) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert v V hv ih =>
      have hcongr : blockProbability U m (fun B => ∃ w ∈ insert v V, P w B) =
          blockProbability U m (fun B => P v B ∨ ∃ w ∈ V, P w B) := by
        apply blockProbability_congr
        intro B hB
        simp
      rw [hcongr, Finset.sum_insert hv]
      exact (blockProbability_or_le U m _ _).trans (add_le_add le_rfl ih)

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.blockProbability_exists_le.{u} := @_root_.OAI.Problem313.blockProbability_exists_le.{u}
