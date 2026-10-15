-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:12:23.596379+00:00
-- url     : https://prove2.me/submissions/ef1fc239-4787-4f50-9a43-522947e5338c

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean:L36-L49
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History

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

lemma attemptLetter_none_iff {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) :
    attemptLetter P Q z = none ↔ ¬ ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R := by
  classical
  by_cases h : ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R
  · rw [attemptLetter,dite_eq_left h]
    simp only [reduceCtorEq,h,not_true_eq_false]
  · rw [attemptLetter,dite_eq_right h]
    simp only [h,not_false_eq_true]

lemma attemptLetter_some_iff {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q R : Cell n)
    (z : Coordinate n) : attemptLetter P Q z = some R ↔ FirstHeavy P Q R ∧ z ∈ cellSet R := by
  classical
  constructor
  · intro he
    have hex : ∃ E : Cell n,FirstHeavy P Q E ∧ z ∈ cellSet E := by
      by_contra h
      rw [(attemptLetter_none_iff P Q z).mpr h] at he
      contradiction
    have hc : hex.choose = R := by
      simpa only [attemptLetter,dite_eq_left hex,Option.some.injEq] using he
    exact hc ▸ hex.choose_spec
  · rintro ⟨hR,hzR⟩
    exact (attemptLetter_eq_iff hn P Q (hR.1.1.2 hzR) (some R)).mpr (by simp only [branch,ite_eq_left hR]; exact hzR)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q R : Cell n)
    (z : Coordinate n) : attemptLetter P Q z = some R ↔ FirstHeavy P Q R ∧ z ∈ cellSet R := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff hn P Q R z
    | exact OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff
    | (apply OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.attemptLetter_some_iff <;> assumption)
