-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:26:52.706797+00:00
-- url     : https://prove2.me/submissions/9dd01337-9abc-4e69-a77c-f351db54f632

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    (∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t => Spos t ω)) ∧
    (∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t => Sneg t ω)) := by
  dsimp only
  have hboth : ∀ᵐ ω ∂P,
      ProbabilityTheory.IsCadlag
        (fun t => (variationOnFromTo (fun s => X s ω) Set.univ 0 t + X t ω) / 2) ∧
      ProbabilityTheory.IsCadlag
        (fun t => (variationOnFromTo (fun s => X s ω) Set.univ 0 t - X t ω) / 2) := by
    filter_upwards [hBV, hX.cadlag_ae] with ω hω hc
    let f : ℝ≥0 → ℝ := fun t => X t ω
    let v := variationOnFromTo f Set.univ 0
    have hv : ProbabilityTheory.IsCadlag v := by
      intro t
      obtain ⟨hr, l, hl⟩ := hc t
      have hr' : Tendsto f (nhdsWithin t (Set.Ioi t)) (nhds (f t)) :=
        hr.mono Set.Ioi_subset_Ici_self
      have hvr := variationOnFromTo.tendsto_right (Set.mem_univ (0 : ℝ≥0))
        (Set.mem_univ t) hω (by simpa only [Set.univ_inter] using hr')
      have hvl := variationOnFromTo.tendsto_left (Set.mem_univ (0 : ℝ≥0))
        (Set.mem_univ t) hω (by simpa only [Set.univ_inter] using hl)
      refine ⟨continuousWithinAt_Ioi_iff_Ici.mp ?_, v t - dist (f t) l, ?_⟩
      · simpa [ContinuousWithinAt, v, f] using hvr
      · simpa only [Set.univ_inter, v] using hvl
    constructor
    · intro t
      obtain ⟨hr, l, hl⟩ := hc t
      obtain ⟨hvr, m, hvl⟩ := hv t
      exact ⟨(hvr.add hr).div_const 2, (m+l)/2, (hvl.add hl).div_const 2⟩
    · intro t
      obtain ⟨hr, l, hl⟩ := hc t
      obtain ⟨hvr, m, hvl⟩ := hv t
      exact ⟨(hvr.sub hr).div_const 2, (m-l)/2, (hvl.sub hl).div_const 2⟩
  exact ⟨hboth.mono (fun _ h => h.1), hboth.mono (fun _ h => h.2)⟩
