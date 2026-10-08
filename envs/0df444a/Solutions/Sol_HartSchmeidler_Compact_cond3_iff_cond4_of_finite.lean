-- Prove2me | solution 1 for HartSchmeidler.Compact.cond3_iff_cond4_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:27:17.078604+00:00
-- url     : https://prove2.me/submissions/6c5d99fd-0d82-4cbc-8e3e-0197a50c90bd

import Definitions.Def_HartSchmeidler_Compact_Game



namespace HartSchmeidler.Compact

open MeasureTheory

lemma c34_meas_update {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    [∀ j, TopologicalSpace (S j)] [∀ j, MeasurableSpace (S j)] [∀ j, BorelSpace (S j)]
    (g : Profile S → ℝ) (hg : Measurable g) (i : ι) (t : S i) :
    Measurable (fun s : Profile S => g (Function.update s i t)) := by
  refine hg.comp (Continuous.measurable ?_)
  show Continuous (fun s : ∀ j, S j => Function.update s i t)
  exact Continuous.update continuous_id i continuous_const

lemma c34_meas_set {ι : Type*} {S : ι → Type*}
    [∀ j, TopologicalSpace (S j)] [∀ j, MeasurableSpace (S j)] [∀ j, BorelSpace (S j)]
    (i : ι) [DiscreteTopology (S i)] (r : S i) :
    MeasurableSet {s : Profile S | s i = r} := by
  have : Measurable (fun s : Profile S => s i) := by
    have : Continuous (fun s : Profile S => s i) := continuous_apply i
    exact this.measurable
  exact this (measurableSet_singleton r)

lemma c34_decomp {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    [∀ j, TopologicalSpace (S j)] [∀ j, MeasurableSpace (S j)] [∀ j, BorelSpace (S j)]
    (h : ι → Profile S → ℝ) (i : ι) [Fintype (S i)] [DiscreteTopology (S i)]
    (hmeas : Measurable (h i)) (M : ℝ) (hbdd : ∀ s, |h i s| ≤ M)
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (ζ : S i → S i) :
    (∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p) =
      ∑ r : S i, ∫ s in {s : Profile S | s i = r}, (h i s - h i (Function.update s i (ζ r))) ∂p := by
  classical
  have hint : ∀ r : S i, Integrable (fun s : Profile S => h i s - h i (Function.update s i (ζ r))) p := by
    intro r
    refine Integrable.sub ?_ ?_
    · exact Integrable.of_bound hmeas.aestronglyMeasurable M (Filter.Eventually.of_forall fun s => by simpa using hbdd s)
    · exact Integrable.of_bound (c34_meas_update (h i) hmeas i _).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun s => by simpa using hbdd _)
  have key : (fun s : Profile S => h i s - h i (Function.update s i (ζ (s i)))) =
      fun s => ∑ r : S i, Set.indicator {s : Profile S | s i = r}
        (fun s => h i s - h i (Function.update s i (ζ r))) s := by
    funext s
    rw [Finset.sum_eq_single (s i)]
    · simp [Set.indicator]
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · simp
  rw [key, integral_finsetSum]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_indicator (c34_meas_set i r)]
  · intro r _
    exact (hint r).indicator (c34_meas_set i r)

theorem c34_core {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    [∀ j, TopologicalSpace (S j)] [∀ j, MeasurableSpace (S j)] [∀ j, BorelSpace (S j)]
    (h : ι → Profile S → ℝ) (i : ι) [Fintype (S i)] [DiscreteTopology (S i)]
    (hmeas : Measurable (h i)) (hbdd : ∃ M : ℝ, ∀ s, |h i s| ≤ M)
    (p : Measure (Profile S)) [IsProbabilityMeasure p] :
    (∀ r t : S i,
        0 ≤ ∫ s in {s : Profile S | s i = r}, (h i s - h i (Function.update s i t)) ∂p) ↔
      (∀ ζ : S i → S i, Measurable ζ →
        0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p) := by
  classical
  obtain ⟨M, hM⟩ := hbdd
  constructor
  · intro H ζ _
    rw [c34_decomp h i hmeas M hM p ζ]
    exact Finset.sum_nonneg fun r _ => H r (ζ r)
  · intro H r t
    have := H (fun x => if x = r then t else x) (measurable_of_finite _)
    have e := c34_decomp h i hmeas M hM p (fun x => if x = r then t else x)
    beta_reduce at e
    rw [e, Finset.sum_eq_single r] at this
    · simpa using this
    · intro b _ hb
      have : ∫ s in {s : Profile S | s i = b}, (h i s - h i (Function.update s i (if b = r then t else b))) ∂p = 0 := by
        rw [setIntegral_congr_fun (c34_meas_set i b) (g := fun _ => (0:ℝ))]
        · simp
        · intro s hs
          have hs' : s i = b := hs
          simp only [if_neg hb]
          rw [← hs']
          have e2 : (Function.update s i (s i) : Profile S) = s := Function.update_eq_self i s
          rw [e2]; simp
      exact this
    · simp

end HartSchmeidler.Compact

open HartSchmeidler.Compact
open MeasureTheory

theorem solution {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    [∀ j, TopologicalSpace (S j)] [∀ j, MeasurableSpace (S j)] [∀ j, BorelSpace (S j)]
    (h : ι → Profile S → ℝ) (i : ι) [Fintype (S i)] [DiscreteTopology (S i)]
    (hmeas : Measurable (h i)) (hbdd : ∃ M : ℝ, ∀ s, |h i s| ≤ M)
    (p : Measure (Profile S)) [IsProbabilityMeasure p] :
    (∀ r t : S i,
        0 ≤ ∫ s in {s : Profile S | s i = r}, (h i s - h i (Function.update s i t)) ∂p) ↔
      (∀ ζ : S i → S i, Measurable ζ →
        0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p) := by
  exact c34_core h i hmeas hbdd p
