-- Prove2me | solution 1 for Kyprianou.Ch02.prmSimpleMarkFibreCountWeightedShiftLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:13:12.766454+00:00
-- url     : https://prove2.me/submissions/9a60d3fb-4b9e-4c88-a19c-69769897734f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteSimpleMarkedSumStationaryAndMeasurableV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Transfer the proved Fin-indexed count law to the finite range of a simple mark. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (s t : ℝ≥0) :
    Measurable (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) ∧
    P.map (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) =
    P.map (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) := by
  classical
  let e : {x : ℝ // x ∈ f.range} ≃ Fin f.range.card :=
    Finset.equivFin f.range
  let C : Fin f.range.card → Set ℝ := fun i =>
    {y : ℝ | f y = (e.symm i).1}
  let w : Fin f.range.card → ℝ := fun i => (e.symm i).1
  have hC : ∀ i, MeasurableSet (C i) := by
    intro i
    exact (measurableSet_singleton (w i)).preimage f.measurable
  have hd : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    have heq : (e.symm i).1 = (e.symm j).1 :=
      hyi.symm.trans hyj
    exact hij ((e.symm.injective (Subtype.ext heq)))
  have hsum (a b : ℝ≥0) (ω : Ω) :
      (∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) =
      ∑ i : Fin f.range.card, w i * (N.N ω
        (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ (B ∩ C i))).toReal := by
    calc
      _ = ∑ x ∈ f.range.attach, x.1 * (N.N ω
          (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x.1}))).toReal :=
            (Finset.sum_attach f.range _).symm
      _ = ∑ i ∈ Finset.univ, w i * (N.N ω
          (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ (B ∩ C i))).toReal := by
        apply Finset.sum_equiv e
        · intro x
          simp
        · intro x hx
          simp only [w, C, e.symm_apply_apply]
      _ = _ := by simp
  have hbase :=
    Kyprianou.Ch02.prmKLSFiniteSimpleMarkedSumStationaryAndMeasurableV1
      P ν N B hB hfinite f.range.card C hC hd w s t
  constructor
  · have h : Measurable (fun ω => ∑ i : Fin f.range.card,
        w i * (N.N ω
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) := hbase.1
    convert h using 1
    funext ω
    exact hsum 0 t ω
  · have h1 : (fun ω : Ω => ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) =
      (fun ω : Ω => ∑ i : Fin f.range.card, w i * (N.N ω
        (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ (B ∩ C i))).toReal) := by
      funext ω
      exact hsum s (s + t) ω
    have h2 : (fun ω : Ω => ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) =
      (fun ω : Ω => ∑ i : Fin f.range.card, w i * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) := by
      funext ω
      exact hsum 0 t ω
    rw [h1, h2]
    exact hbase.2
