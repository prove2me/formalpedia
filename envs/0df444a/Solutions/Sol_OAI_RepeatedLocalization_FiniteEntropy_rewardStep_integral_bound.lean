-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:30:26.760358+00:00
-- url     : https://prove2.me/submissions/48726a80-e3ba-4553-ad47-e0bf327a1205

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/RewardBounds.lean:L118-L138
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_attemptLetter
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_measurable_run
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_partition_integral_bound
import Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_run_eq_iff_mem
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

lemma measurableSet_cellSet {n : ℕ} (Q : Cell n) : MeasurableSet (cellSet Q) := by
  rw [cellSet_eq_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

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

lemma measurableSet_residual {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    MeasurableSet (residual P Q) :=
  (measurableSet_cellSet Q).diff (MeasurableSet.iUnion (fun R => measurableSet_cellSet R.val))

lemma measurableSet_branch {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (a : Letter n) :
    MeasurableSet (branch P Q a) := by
  classical
  cases a with
  | none => exact measurableSet_residual P Q
  | some R => by_cases h : FirstHeavy P Q R <;> simp [branch,h,measurableSet_cellSet]

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

lemma state_event_measurable {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    MeasurableSet (state P Q h).event := by
  induction h using List.reverseRecOn with
  | nil => exact measurableSet_cellSet Q
  | append_singleton h a ih =>
    rw [state_append]
    unfold update
    split
    · exact ih
    · exact ih.inter (measurableSet_branch _ _ _)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.ConditionalLaws ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma run_fiber_ae_event {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    {w | run P Q N w = run P Q N z} =ᵐ[P] (state P Q (run P Q N z)).event := by
  filter_upwards [hroot] with w hw
  exact propext (run_eq_iff_mem hn P Q N hz hw)

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.Rewards ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma cond_event_mul {α : Type*} [MeasurableSpace α] (P : Measure α) [IsFiniteMeasure P]
    {E B : Set α} (hE : MeasurableSet E) (hp : P E ≠ 0) :
    (P (E∩B)).toReal = (P E).toReal * ((ProbabilityTheory.cond P E) B).toReal := by
  rw [ProbabilityTheory.cond_apply hE,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hp' : (P E).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp,measure_ne_top _ _⟩
  exact (mul_inv_cancel_left₀ hp' _).symm

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.CountableIntegrals ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma integral_comp_fiber {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : α → ι) (F : ι → ℝ) (i : ι) (hi : MeasurableSet {x | L x = i}) :
    (∫ x in {x | L x = i},F (L x) ∂μ) = (μ {x | L x = i}).toReal * F i := by
  rw [setIntegral_congr_fun hi (fun x hx => congrArg F hx)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- from OAI.Probability.Localization.RewardBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma reward_only_none {n : ℕ} (r : State n → Letter n → ℝ)
    (hr : ∀ s R,r s (some R) = 0) (s : State n) (a : Letter n) :
    r s a = if a = none then r s none else 0 := by
  cases a <;> simp [hr]

lemma integrable_fixed_reward {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (r : State n → Letter n → ℝ) (hr : ∀ s R,r s (some R) = 0)
    (s : State n) :
    Integrable (fun z => r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z)) P := by
  classical
  have he : (fun z => r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z)) =
      {z | attemptLetter (ProbabilityTheory.cond P s.event) s.cell z = none}.indicator (fun _ => r s none) := by
    funext z
    rw [reward_only_none r hr,Set.indicator_apply]
    rfl
  rw [he]
  exact (integrable_const _).indicator ((measurable_attemptLetter hn _ _) (measurableSet_singleton none))

lemma integral_fixed_reward_event {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (r : State n → Letter n → ℝ) (hr : ∀ s R,r s (some R) = 0)
    (s : State n) (hmeas : MeasurableSet s.event) (hsub : s.event ⊆ cellSet s.cell)
    (hp : P s.event ≠ 0) :
    (∫ z in s.event,r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z) ∂P) =
      (P s.event).toReal * (complementMass P s * r s none) := by
  classical
  let B := residual (ProbabilityTheory.cond P s.event) s.cell
  have hB : MeasurableSet B := measurableSet_residual _ _
  have he : ∀ z ∈ s.event,r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z) =
      B.indicator (fun _ => r s none) z := by
    intro z hz
    rw [reward_only_none r hr,Set.indicator_apply]
    have hh : attemptLetter (ProbabilityTheory.cond P s.event) s.cell z = none ↔ z ∈ B :=
      attemptLetter_eq_iff hn _ _ (hsub hz) none
    exact if_congr hh rfl rfl
  rw [setIntegral_congr_fun hmeas he,integral_indicator hB,Measure.restrict_restrict hB,
    Set.inter_comm B s.event,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    cond_event_mul P hmeas hp]
  exact mul_assoc _ _ _

lemma exists_run_fiber_root {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) (h : Log n)
    (hp : P {z | run P Q N z = h} ≠ 0) :
    ∃ z,z ∈ cellSet Q ∧ run P Q N z = h := by
  have he : ({z | run P Q N z = h} ∩ cellSet Q : Set (Coordinate n)) =ᵐ[P] {z | run P Q N z = h} := by
    filter_upwards [hroot] with z hz
    change (run P Q N z = h ∧ z ∈ cellSet Q) = (run P Q N z = h)
    simp only [hz,and_true]
  have hp' : P ({z | run P Q N z = h} ∩ cellSet Q) ≠ 0 := by
    rw [measure_congr he]; exact hp
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hp'
  exact ⟨z,hz.2,hz.1⟩

lemma rewardStep_fiber_integrable {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (r : State n → Letter n → ℝ)
    (hr : ∀ s R,r s (some R) = 0) (N : ℕ) (h : Log n) :
    IntegrableOn (rewardStep P Q r N) {z | run P Q N z = h} P := by
  apply (integrable_fixed_reward hn P r hr (state P Q h)).integrableOn.congr_fun
    (s := {z | run P Q N z = h})
  · intro z hz
    change run P Q N z = h at hz
    simp only [rewardStep,hz]
  · exact (measurable_run hn P Q N) (measurableSet_singleton h)

lemma rewardStep_fiber_integral {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q)
    (r : State n → Letter n → ℝ) (hr : ∀ s R,r s (some R) = 0) (N : ℕ) (h : Log n) :
    (∫ z in {z | run P Q N z = h},rewardStep P Q r N z ∂P) =
      (P {z | run P Q N z = h}).toReal * (complementMass P (state P Q h) * r (state P Q h) none) := by
  by_cases hp : P {z | run P Q N z = h} = 0
  · rw [Measure.restrict_eq_zero.mpr hp,hp,integral_zero_measure,ENNReal.toReal_zero,zero_mul]
  obtain ⟨z,hz,hzh⟩ := exists_run_fiber_root P Q hroot N h hp
  have he : {w | run P Q N w = h} =ᵐ[P] (state P Q h).event := by
    simpa only [hzh] using run_fiber_ae_event hn P Q hroot N hz
  have hpe : P (state P Q h).event ≠ 0 := by rwa [← measure_congr he]
  have hm : MeasurableSet {z | run P Q N z = h} := (measurable_run hn P Q N) (measurableSet_singleton h)
  rw [setIntegral_congr_fun hm
    (g := fun z => r (state P Q h) (attemptLetter (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell z))
    (fun w hw => by change run P Q N w = h at hw; simp only [rewardStep,hw])]
  rw [Measure.restrict_congr_set he,measure_congr he]
  exact integral_fixed_reward_event hn P r hr _ (state_event_measurable P Q h)
    (state_event_subset_cell P Q h) hpe

lemma integrable_activeIndicator {n : ℕ} (P : Measure (Coordinate n)) [IsFiniteMeasure P]
    (Q : Cell n) (hn : 0 < n) (N : ℕ) : Integrable (activeIndicator P Q N) P := by
  have he : activeIndicator P Q N = {z | (state P Q (run P Q N z)).stopped = false}.indicator (fun _ => (1:ℝ)) := by
    funext z
    simp only [activeIndicator,Set.indicator_apply,Set.mem_ofPred_eq]
    by_cases hs : (state P Q (run P Q N z)).stopped = true
    · simp [hs]
    · simp [Bool.eq_false_iff.mpr hs]
  rw [he]
  exact (integrable_const _).indicator
    (((measurable_of_countable (fun h : Log n => (state P Q h).stopped)).comp
      (measurable_run hn P Q N)) (measurableSet_singleton false))

lemma rewardStep_integral_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q)
    (r : State n → Letter n → ℝ) (hr0 : ∀ s a,0 ≤ r s a)
    (hr : ∀ s R,r s (some R) = 0) (b : ℝ)
    (hb : ∀ s, complementMass P s * r s none ≤ b*(if s.stopped then 0 else 1)) (N : ℕ) :
    Integrable (rewardStep P Q r N) P ∧
      (∫ z,rewardStep P Q r N z ∂P) ≤ b*(∫ z,activeIndicator P Q N z ∂P) := by
  have hb' (h : Log n) : (∫ z in {z | run P Q N z = h},rewardStep P Q r N z ∂P) ≤
      ∫ z in {z | run P Q N z = h},b*activeIndicator P Q N z ∂P := by
    rw [rewardStep_fiber_integral hn P Q hroot r hr N h]
    change _ ≤ ∫ z in {z | run P Q N z = h},
      (fun h : Log n => b*(if (state P Q h).stopped then 0 else 1)) (run P Q N z) ∂P
    rw [integral_comp_fiber P (run P Q N)
      (fun h : Log n => b*(if (state P Q h).stopped then 0 else 1)) h
      ((measurable_run hn P Q N) (measurableSet_singleton h))]
    exact mul_le_mul_of_nonneg_left (hb _) ENNReal.toReal_nonneg
  have hi := partition_integral_bound P (run P Q N) (measurable_run hn P Q N)
    (fun z => hr0 _ _) (rewardStep_fiber_integrable hn P Q r hr N)
    ((integrable_activeIndicator P Q hn N).const_mul b) hb'
  rw [integral_const_mul] at hi
  exact hi

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q)
    (r : State n → Letter n → ℝ) (hr0 : ∀ s a,0 ≤ r s a)
    (hr : ∀ s R,r s (some R) = 0) (b : ℝ)
    (hb : ∀ s, complementMass P s * r s none ≤ b*(if s.stopped then 0 else 1)) (N : ℕ) :
    Integrable (rewardStep P Q r N) P ∧
      (∫ z,rewardStep P Q r N z ∂P) ≤ b*(∫ z,activeIndicator P Q N z ∂P) := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound hn P Q hroot r hr0 hr b hb N
    | exact OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound
    | (apply OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.rewardStep_integral_bound <;> assumption)
