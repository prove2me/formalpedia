-- Prove2me | solution 1 for Kyprianou.Ch02.prmKLSFiniteSimpleMarkedSumStationaryAndMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:14:23.951796+00:00
-- url     : https://prove2.me/submissions/74adae39-ef6a-4063-b82c-707597ba9c57

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteVectorShiftCountLawV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (w : Fin n → ℝ) (s t : ℝ≥0) :
    Measurable (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) ∧
    P.map (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ (B ∩ C i))).toReal) = P.map (fun (ω : Ω) =>
        ∑ i : Fin n, (w i) *
          (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) := by
  classical
  constructor
  · refine Finset.measurable_sum _ (fun i _ => ?_)
    exact measurable_const.mul
      (ENNReal.measurable_toReal.comp
        (N.measurable_eval (measurableSet_Ioc.prod (hB.inter (hC i)))))
  · let A : Fin n → Set ℝ := fun i => B ∩ C i
    have hm : ∀ i, MeasurableSet (A i) :=
      fun i => hB.inter (hC i)
    have hf : ∀ i, ν (A i) < ⊤ := by
      intro i
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
    have hd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      exact Set.disjoint_left.mp (hdisj hij) hxi.2 hxj.2
    let FS : (Fin n → ℝ≥0∞) → ℝ := fun v =>
      ∑ i : Fin n, (w i) * (v i).toReal
    have hmFS : Measurable FS := by
      refine Finset.measurable_sum _ (fun i _ => ?_)
      exact measurable_const.mul
        (ENNReal.measurable_toReal.comp (measurable_pi_apply i))
    have hmStart : Measurable (fun (ω : Ω) (i : Fin n) =>
        N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A i)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact N.measurable_eval (measurableSet_Ioc.prod (hm i))
    have hmShift : Measurable (fun (ω : Ω) (i : Fin n) =>
        N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ A i)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact N.measurable_eval (measurableSet_Ioc.prod (hm i))
    have hv := Kyprianou.Ch02.prmKLSFiniteVectorShiftCountLawV1
      P ν N n A hm hf hd s t
    have hmap := congrArg (fun m : Measure (Fin n → ℝ≥0∞) => m.map FS) hv
    change P.map (FS ∘ (fun ω i =>
      N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ A i))) =
      P.map (FS ∘ (fun ω i =>
      N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ A i)))
    rw [← Measure.map_map hmFS hmShift, ← Measure.map_map hmFS hmStart]
    exact hmap
