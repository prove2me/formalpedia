-- Prove2me | solution 1 for Kyprianou.Ch02.prmCompensatedFiniteRegionCadlagAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:49:46.04714+00:00
-- url     : https://prove2.me/submissions/648c3513-e7c7-46a6-9c53-4cdd08f81ffd

import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagAEV1
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (c : ℝ) :
    ∀ᵐ ω ∂P,
      ProbabilityTheory.IsCadlag (fun (t : ℝ≥0) =>
        (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))
          - (t : ℝ) * c) := by
  have hraw := Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 P ν N B hB hfinite
  have hcont : Continuous (fun t : ℝ≥0 => -((t : ℝ) * c)) :=
    (NNReal.continuous_coe.mul continuous_const).neg
  have hdrift : ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => -((t : ℝ) * c)) := by
    change ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => -((s : ℝ) * c)) (Set.Ici t) t ∧
      ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => -((s : ℝ) * c))
        (nhdsWithin t (Set.Iio t)) (nhds l)
    intro t
    refine ⟨hcont.continuousAt.continuousWithinAt, ?_⟩
    exact ⟨_, (hcont.tendsto t).mono_left nhdsWithin_le_nhds⟩
  filter_upwards [hraw] with ω hω
  have hadd := ProbabilityTheory.IsCadlag.add hω hdrift
  simpa only [sub_eq_add_neg] using hadd
