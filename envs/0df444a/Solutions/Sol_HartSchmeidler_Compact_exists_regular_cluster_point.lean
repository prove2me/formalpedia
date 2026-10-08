-- Prove2me | solution 1 for HartSchmeidler.Compact.exists_regular_cluster_point
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:35:08.165426+00:00
-- url     : https://prove2.me/submissions/84009770-deee-48c2-b5e0-7a08f69b8882

import Mathlib



namespace HartSchmeidler.Compact

open MeasureTheory

theorem erc_core {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure X) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure X, IsProbabilityMeasure p ∧ p.Regular ∧
      ∀ (fs : Finset C(X, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D, ∃ d : D, d₀ ≤ d ∧
        ∀ f ∈ fs, |∫ x, f x ∂p - ∫ x, f x ∂(q d)| < ε := by
  classical
  let q' : D → ProbabilityMeasure X := fun d => ⟨q d, hq d⟩
  obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace (Filter.map q' Filter.atTop)
  obtain ⟨p, hpR, hpF, hpint⟩ := Measure.exists_regular_eq_of_compactSpace (ν : Measure X)
  have hpP : IsProbabilityMeasure p := by
    constructor
    have := hpint (BoundedContinuousFunction.const X 1)
    simp at this
    have h2 : (p Set.univ).toReal = 1 := by simpa [measureReal_def] using this.symm
    rw [← ENNReal.ofReal_toReal (measure_ne_top p Set.univ), h2]; simp
  refine ⟨p, hpP, hpR, ?_⟩
  intro fs ε hε d₀
  let I : C(X, ℝ) → ProbabilityMeasure X → ℝ := fun f m => ∫ x, f x ∂(m : Measure X)
  have hI : ∀ f, Continuous (I f) := fun f =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (BoundedContinuousFunction.mkOfCompact f)
  let U : Set (ProbabilityMeasure X) := ⋂ f ∈ fs, {m | |I f ν - I f m| < ε}
  have hU : U ∈ nhds ν := by
    apply (Filter.biInter_finset_mem fs).2
    intro f _
    apply IsOpen.mem_nhds _ (by simpa using hε)
    exact isOpen_lt (by fun_prop) continuous_const
  have hfreq := (mapClusterPt_iff_frequently.1 hν) U hU
  obtain ⟨d, hd, hdU⟩ := Filter.frequently_atTop.1 hfreq d₀
  refine ⟨d, hd, fun f hf => ?_⟩
  have h1 := Set.mem_iInter₂.1 hdU f hf
  have h2 : ∫ x, f x ∂p = I f ν := (hpint (BoundedContinuousFunction.mkOfCompact f)).symm
  rw [h2]; exact h1

end HartSchmeidler.Compact

open HartSchmeidler.Compact
open MeasureTheory

theorem solution {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    {D : Type*} [Preorder D] [IsDirected D (· ≤ ·)] [Nonempty D]
    (q : D → Measure X) (hq : ∀ d, IsProbabilityMeasure (q d)) :
    ∃ p : Measure X, IsProbabilityMeasure p ∧ p.Regular ∧
      ∀ (fs : Finset C(X, ℝ)) (ε : ℝ), 0 < ε → ∀ d₀ : D, ∃ d : D, d₀ ≤ d ∧
        ∀ f ∈ fs, |∫ x, f x ∂p - ∫ x, f x ∂(q d)| < ε := by
  exact erc_core q hq
