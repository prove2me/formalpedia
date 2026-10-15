-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.truncatedDepth_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:43:22.387064+00:00
-- url     : https://prove2.me/submissions/4466d72e-5ab9-44d8-b5df-ee58bbfa49e3

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Termination.lean:L65-L85
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.truncatedDepth_mono. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Definitions.Def_OAI_Probability_Localization_EntropyBudget
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_run_mem_event
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_state_event_subset_cell

-- ---- from OAI.Probability.Localization.Cells ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

lemma cellWidth_pos {n J : ℕ} (hn : 0 < n) : 0 < cellWidth n J := by
  unfold cellWidth
  positivity

lemma cellSet_eq_pi {n : ℕ} (Q : Cell n) :
    cellSet Q = Set.pi univ (fun i => Ico (cellLower Q i) (cellLower Q i + cellWidth n Q.1)) := by
  ext z
  simp only [cellSet, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ico]
  congr! 3
  simp only [cellLower, cellWidth]
  ring

lemma cellIndex_eq_of_mem {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : cellIndex Q.1 z = Q.2 := by
  funext i
  apply Fin.ext
  simp only [cellSet, mem_ofPred_eq, neg_div] at hz
  have hd : 0 < Real.sqrt (n : ℝ) * (2 : ℝ)^Q.1 := by positivity
  let x : ℝ := (z i + 1 / (2 * Real.sqrt n)) * (Real.sqrt n * (2 : ℝ)^Q.1)
  have hl : (Q.2 i : ℝ) ≤ x := by
    apply (div_le_iff₀ hd).mp
    linarith [(hz i).1]
  have hu : x < (Q.2 i : ℝ) + 1 := by
    apply (lt_div_iff₀ hd).mp
    linarith [(hz i).2]
  have hf : ⌊x⌋₊ = (Q.2 i).val := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg _) hl)).mpr ⟨hl, hu⟩
  change ⌊x⌋₊ % 2^Q.1 = (Q.2 i).val
  rw [hf, Nat.mod_eq_of_lt (Q.2 i).isLt]

lemma cellWidth_add (n J l : ℕ) :
    cellWidth n (J + l) = cellWidth n J / (2 : ℝ)^l := by
  simp only [cellWidth, pow_add]
  ring

lemma childCell_lower {n : ℕ} (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) (i : Fin n) :
    cellLower (childCell Q l a) i = cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) := by
  simp only [cellLower, cellWidth, childCell, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    pow_add]
  have ht : (2 : ℝ)^l ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

lemma childCell_subset {n : ℕ} (hn : 0 < n) (Q : Cell n) (l : ℕ) (a : Fin n → Fin (2^l)) :
    cellSet (childCell Q l a) ⊆ cellSet Q := by
  rw [cellSet_eq_pi, cellSet_eq_pi]
  intro z hz i hi
  have hz' := hz i hi
  have hw := cellWidth_pos (J := Q.1+l) hn
  have hidx : (a i : ℝ) + 1 ≤ (2 : ℝ)^l := by exact_mod_cast (a i).isLt
  have he : cellWidth n (Q.1+l) * (2 : ℝ)^l = cellWidth n Q.1 := by
    rw [cellWidth_add, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]
  dsimp only at hz'
  rw [childCell_lower] at hz'
  change cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) ≤ z i ∧
    z i < cellLower Q i + cellWidth n (Q.1+l) * (a i : ℝ) + cellWidth n (Q.1+l) at hz'
  have hu := mul_le_mul_of_nonneg_left hidx hw.le
  rw [he] at hu
  have ha : (0 : ℝ) ≤ (a i : ℝ) := Nat.cast_nonneg _
  exact ⟨by nlinarith [hz'.1], by nlinarith [hz'.2]⟩

lemma cell_ext {n : ℕ} {Q R : Cell n} (h : Q.1 = R.1)
    (hi : ∀ i,(Q.2 i).val = (R.2 i).val) : Q = R := by
  rcases Q with ⟨J,a⟩
  rcases R with ⟨K,b⟩
  dsimp at h hi
  subst K
  congr 1
  funext i
  exact Fin.ext (hi i)

lemma child_ancestorCell {n : ℕ} (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) :
    childCell (ancestorCell Q J hJ) (Q.1-J)
      (fun i => ⟨(Q.2 i).val % 2^(Q.1-J),Nat.mod_lt _ (by positivity)⟩) = Q := by
  apply cell_ext (Nat.add_sub_of_le hJ)
  intro i
  change (Q.2 i).val / 2^(Q.1-J) * 2^(Q.1-J) + (Q.2 i).val % 2^(Q.1-J) = (Q.2 i).val
  simpa only [Nat.mul_comm] using Nat.div_add_mod (Q.2 i).val (2^(Q.1-J))

lemma cellSet_subset_ancestor {n : ℕ} (hn : 0 < n) (Q : Cell n) (J : ℕ) (hJ : J ≤ Q.1) :
    cellSet Q ⊆ cellSet (ancestorCell Q J hJ) := by
  have h := childCell_subset hn (ancestorCell Q J hJ) (Q.1-J)
    (fun i => ⟨(Q.2 i).val % 2^(Q.1-J),Nat.mod_lt _ (by positivity)⟩)
  rwa [child_ancestorCell] at h

lemma cellAt_eq_of_mem {n : ℕ} (hn : 0 < n) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : cellAt Q.1 z = Q := by
  apply cell_ext (Q := cellAt Q.1 z) (R := Q) rfl
  have h := cellIndex_eq_of_mem hn Q hz
  intro i
  exact congrArg Fin.val (congrFun h i)

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.FirstHeavy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma nested_of_point {n : ℕ} (hn : 0 < n) {Q R : Cell n} (h : Q.1 ≤ R.1)
    {z : Coordinate n} (hzQ : z ∈ cellSet Q) (hzR : z ∈ cellSet R) : Descendant Q R := by
  have ha := cellSet_subset_ancestor hn R Q.1 h
  have h₁ := cellAt_eq_of_mem hn Q hzQ
  have h₂ := cellAt_eq_of_mem hn (ancestorCell R Q.1 h) (ha hzR)
  have he : ancestorCell R Q.1 h = Q := h₂.symm.trans h₁
  exact ⟨h,by simpa only [he] using ha⟩

lemma firstHeavy_disjoint {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {R S : Cell n} (hR : FirstHeavy P Q R) (hS : FirstHeavy P Q S) (hne : R ≠ S) :
    Disjoint (cellSet R) (cellSet S) := by
  apply Set.disjoint_left.mpr
  intro z hzR hzS
  rcases le_total R.1 S.1 with h | h
  · exact hne (hS.2 R hR.1 (nested_of_point hn h hzR hzS))
  · exact hne (hR.2 S hS.1 (nested_of_point hn h hzS hzR)).symm

lemma branch_disjoint {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {a b : Letter n} (hab : a ≠ b) : Disjoint (branch P Q a) (branch P Q b) := by
  classical
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hab rfl)
    | some R =>
      by_cases h : FirstHeavy P Q R
      · simp only [branch,ite_eq_left h]
        apply Set.disjoint_left.mpr
        intro z hz hzR
        exact hz.2 (Set.mem_iUnion.mpr ⟨⟨R,h⟩,hzR⟩)
      · simp [branch,h]
  | some R =>
    cases b with
    | none =>
      by_cases h : FirstHeavy P Q R
      · simp only [branch,ite_eq_left h]
        apply Set.disjoint_right.mpr
        intro z hz hzR
        exact hz.2 (Set.mem_iUnion.mpr ⟨⟨R,h⟩,hzR⟩)
      · simp [branch,h]
    | some S =>
      by_cases hR : FirstHeavy P Q R
      · by_cases hS : FirstHeavy P Q S
        · simpa only [branch,ite_eq_left hR,ite_eq_left hS] using
            firstHeavy_disjoint hn P Q hR hS (fun h => hab (congrArg some h))
        · simp [branch,hS]
      · simp [branch,hR]

lemma attemptLetter_mem_branch {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : z ∈ branch P Q (attemptLetter P Q z) := by
  classical
  by_cases h : ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R
  · simp only [attemptLetter,dite_eq_left h,branch,ite_eq_left h.choose_spec.1]
    exact h.choose_spec.2
  · simp only [attemptLetter,dite_eq_right h,branch,residual]
    refine ⟨hz,?_⟩
    intro hm
    obtain ⟨R,hR⟩ := Set.mem_iUnion.mp hm
    exact h ⟨R.val,R.property,hR⟩

lemma attemptLetter_eq_iff {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) (a : Letter n) :
    attemptLetter P Q z = a ↔ z ∈ branch P Q a := by
  constructor
  · intro he; rw [← he]; exact attemptLetter_mem_branch P Q hz
  · intro hm
    by_contra he
    exact Set.disjoint_left.mp (branch_disjoint hn P Q he) (attemptLetter_mem_branch P Q hz) hm

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.History ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma state_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    state P Q (h++[a]) = update P (state P Q h) a := by
  simp only [state,List.foldl_append,List.foldl_cons,List.foldl_nil]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Termination ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

open Filter
open scoped Topology

lemma truncatedDepth_mono {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : Monotone (fun N => truncatedDepth P Q N z) := by
  classical
  apply monotone_nat_of_le_succ
  intro N
  by_cases hs : (state P Q (run P Q N z)).stopped = true
  · simp only [truncatedDepth,run,hs,ite_true,le_refl]
  let s := state P Q (run P Q N z)
  let a := attemptLetter (ProbabilityTheory.cond P s.event) s.cell z
  have erun : run P Q (N+1) z = run P Q N z ++ [a] := by simp only [run,hs,Bool.false_eq_true,ite_false]; rfl
  simp only [truncatedDepth,erun,state_append,update,hs,Bool.false_eq_true,ite_false]
  cases ha : a with
  | none => simp only [Option.getD_none,le_refl]
  | some R =>
    have hcell := state_event_subset_cell P Q _ (run_mem_event P Q N hz)
    have hbranch : z ∈ branch (ProbabilityTheory.cond P s.event) s.cell (some R) :=
      (attemptLetter_eq_iff hn _ _ hcell (some R)).mp ha
    have hR : FirstHeavy (ProbabilityTheory.cond P s.event) s.cell R := by
      by_contra hR
      simp only [branch,ite_eq_right hR,Set.mem_empty_iff_false] at hbranch
    exact Nat.sub_le_sub_right hR.1.1.1 Q.1

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Filter
open scoped Topology

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : Monotone (fun N => truncatedDepth P Q N z) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncatedDepth_mono hn P Q hz
    | exact OAI.RepeatedLocalization.FiniteEntropy.truncatedDepth_mono
    | (apply OAI.RepeatedLocalization.FiniteEntropy.truncatedDepth_mono <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.truncatedDepth_mono <;> assumption)
