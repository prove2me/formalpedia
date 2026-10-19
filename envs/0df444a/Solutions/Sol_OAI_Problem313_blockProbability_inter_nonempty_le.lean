-- Prove2me | solution 1 for OAI.Problem313.blockProbability_inter_nonempty_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:10:56.411649+00:00
-- url     : https://prove2.me/submissions/067758de-e92e-4efc-aaf8-f03574c7beba

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean:L227-L245
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.blockProbability_inter_nonempty_le. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_blockProbability_exists_le

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

theorem blockProbability_mem_count (U : Finset α) {m : ℕ} {u : α}
    (hu : u ∈ U) (hm : 1 ≤ m) :
    ((U.powersetCard m).filter (fun B => u ∈ B)).card =
      (U.card - 1).choose (m - 1) := by
  classical
  simpa using Finset.card_filter_powersetCard_subset {u} U m
    (Finset.singleton_subset_iff.mpr hu) (by simpa using hm)

theorem choose_pred_ratio {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((n - 1).choose (m - 1) : ℝ) / n.choose m = (m : ℝ) / n := by
  have hn : 1 ≤ n := hm.trans hmn
  have hchoose : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hid := Nat.add_one_mul_choose_eq (n - 1) (m - 1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hm] at hid
  have hid' : (n : ℝ) * ((n - 1).choose (m - 1) : ℝ) =
      (n.choose m : ℝ) * m := by exact_mod_cast hid
  apply (div_eq_div_iff hchoose hn0).mpr
  nlinarith

theorem blockProbability_mem (U : Finset α) {m : ℕ} {u : α}
    (hu : u ∈ U) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => u ∈ B) = (m : ℝ) / U.card := by
  classical
  rw [blockProbability_eq, blockProbability_mem_count U hu hm, Finset.card_powersetCard]
  exact choose_pred_ratio hm hmn

omit [DecidableEq α] in
theorem blockProbability_congr (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B ↔ Q B) :
    blockProbability U m P = blockProbability U m Q := by
  apply le_antisymm
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mp)
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mpr)

/-- At most the sum of the individual inclusion probabilities can touch a fixed set. -/
theorem blockProbability_inter_nonempty_le (U E : Finset α) {m : ℕ}
    (hEU : E ⊆ U) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => (B ∩ E).Nonempty) ≤
      (E.card : ℝ) * m / U.card := by
  classical
  calc
    _ = blockProbability U m (fun B => ∃ v ∈ E, v ∈ B) := by
      apply blockProbability_congr
      intro B hB
      simp only [Finset.Nonempty, Finset.mem_inter]
      aesop
    _ ≤ ∑ v ∈ E, blockProbability U m (fun B => v ∈ B) :=
      blockProbability_exists_le U m E (fun v B => v ∈ B)
    _ = ∑ _v ∈ E, (m : ℝ) / U.card := by
      apply Finset.sum_congr rfl
      intro v hv
      exact blockProbability_mem U (hEU hv) hm hmn
    _ = _ := by simp [nsmul_eq_mul, mul_div_assoc]

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.blockProbability_inter_nonempty_le.{u} := @_root_.OAI.Problem313.blockProbability_inter_nonempty_le.{u}
