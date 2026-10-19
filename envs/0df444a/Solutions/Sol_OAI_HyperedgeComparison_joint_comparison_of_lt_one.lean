-- Prove2me | solution 1 for OAI.HyperedgeComparison.joint_comparison_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:14:26.560671+00:00
-- url     : https://prove2.me/submissions/38c6802f-5338-44ac-b433-dd3057daa097

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L1582-L1600
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.joint_comparison_of_lt_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Theorems.Thm_OAI_HyperedgeComparison_expectation_comparison

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

theorem eventProb_compl (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p (fun ω => ¬P ω) = 1 - eventProb p P := by
  unfold eventProb
  calc
    _ = ∫ ω, (1:ℝ) - if P ω then 1 else 0 ∂law p := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : P ω <;> simp [h]
    _ = _ := by
      rw [integral_sub (Integrable.of_finite) (Integrable.of_finite)]
      simp

omit [Fintype E] in
theorem jointObservable_nonneg (A T U : Set V) : 0 ≤ jointObservable A T U := by
  unfold jointObservable
  split_ifs <;> norm_num

omit [Fintype E] in
theorem jointObservable_monotone (A T : Set V) : Monotone (jointObservable A T) := by
  intro U U' hUU
  unfold jointObservable
  split_ifs with h h'
  · rfl
  · obtain ⟨⟨a, ha, hau⟩, ⟨t, ht, htu⟩⟩ := h
    exact (h' ⟨⟨a, ha, hUU hau⟩, ⟨t, ht, hUU htu⟩⟩).elim
  · norm_num
  · rfl

theorem expectation_jointObservable {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (A T : Set V) (i : Fin n) :
    expectationVector H p x (jointObservable A T) i =
      eventProb p (fun ω => Meets H ω ∅ (x i) A ∧ Meets H ω ∅ (x i) T) := by
  unfold expectationVector eventProb
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  unfold jointObservable Meets cluster
  split_ifs <;> first | rfl | simp_all

theorem expectation_jointObservable_of_mem {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (A T : Set V) (i : Fin n) (hi : x i ∈ A) :
    expectationVector H p x (jointObservable A T) i =
      eventProb p (fun ω => Meets H ω ∅ (x i) T) := by
  rw [expectation_jointObservable]
  unfold eventProb
  have ha (ω : E → Bool) : Meets H ω ∅ (x i) A := ⟨x i, hi, .refl⟩
  simp only [ha, true_and]

theorem last_diagonal_avoidance {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin (n+1) → V) :
    baseMatrix H p x (Fin.last n) (Fin.last n) =
      1 - eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))) := by
  rw [← eventProb_compl]
  unfold baseMatrix column eventProb
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hf : firstRoot H x ω ∅ (Fin.last n) (Fin.last n) ↔
      ¬Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n)) := by
    constructor
    · rintro ⟨hd, _⟩ ⟨a, ha, hc⟩
      exact Set.disjoint_left.mp hd hc ha
    · intro h
      refine ⟨Set.disjoint_left.mpr ?_, .refl⟩
      intro a hc ha
      exact h ⟨a, ha, hc⟩
  by_cases h : Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))
  · simp only [hf, h, not_true_eq_false, ite_false]
  · simp only [hf, h, not_false_eq_true, ite_true]

theorem joint_comparison_list [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n+1) → V) (hx : Function.Injective x) (T : Set V) (b : ℝ)
    (hb : ∀ j ≠ Fin.last n, b ≤ eventProb p (fun ω => Meets H ω ∅ (x j) T)) :
    b * eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))) ≤
      eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n)) ∧
        Meets H ω ∅ (x (Fin.last n)) T) := by
  have h := expectation_comparison H p hp x hx
    (jointObservable (earlier x (Fin.last n)) T)
    (jointObservable_nonneg _ _) (jointObservable_monotone _ _) b (by
      intro j hj
      have hm : x j ∈ earlier x (Fin.last n) :=
        ⟨j, Fin.lt_last_iff_ne_last.mpr hj, rfl⟩
      rw [expectation_jointObservable_of_mem H p x (earlier x (Fin.last n)) T j hm]
      exact hb j hj)
  rw [last_diagonal_avoidance] at h
  simpa only [sub_sub_cancel, expectation_jointObservable] using h

omit [Fintype E] in

theorem exists_target_list [Fintype V] (A : Set V) (o : V) (ho : o ∉ A) :
    ∃ n : ℕ, ∃ x : Fin (n+1) → V, Function.Injective x ∧
      x (Fin.last n) = o ∧ earlier x (Fin.last n) = A := by
  classical
  let n := Fintype.card A
  let e : Fin n ≃ A := (Fintype.equivFin A).symm
  let x : Fin (n+1) → V := Fin.snoc (fun i => (e i).1) o
  refine ⟨n, x, ?_, by simp [x], ?_⟩
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact fun _ => rfl
      | cast j =>
        intro h
        have heq : o = (e j).1 := by simpa [x] using h
        exact (ho (heq ▸ (e j).2)).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        intro h
        have heq : (e i).1 = o := by simpa [x] using h
        exact (ho (heq ▸ (e i).2)).elim
      | cast j =>
        intro h
        have heq : (e i).1 = (e j).1 := by simpa [x] using h
        exact congrArg Fin.castSucc (e.injective (Subtype.ext heq))
  · ext a
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
      simp [x, (e i).2]
    · intro ha
      let i := e.symm ⟨a, ha⟩
      refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
      simp [x, i]

/-- The joint connection inequality for arbitrary finite targets, first for
strictly subunit hyperedge probabilities. -/
theorem joint_comparison_of_lt_one [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    b * eventProb p (fun ω => Meets H ω ∅ o A) ≤
      eventProb p (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T) := by
  by_cases ho : o ∈ A
  · have ha (ω : E → Bool) : Meets H ω ∅ o A := ⟨o, ho, .refl⟩
    have h := hb o ho
    simpa [eventProb, ha] using h
  · obtain ⟨n, x, hx, hxo, hxA⟩ := exists_target_list A o ho
    have h := joint_comparison_list H p hp x hx T b (by
      intro j hj
      apply hb
      rw [← hxA]
      exact ⟨j, Fin.lt_last_iff_ne_last.mpr hj, rfl⟩)
    simpa only [hxo, hxA] using h

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.joint_comparison_of_lt_one.{uE,uV} := @_root_.OAI.HyperedgeComparison.joint_comparison_of_lt_one.{uE,uV}
