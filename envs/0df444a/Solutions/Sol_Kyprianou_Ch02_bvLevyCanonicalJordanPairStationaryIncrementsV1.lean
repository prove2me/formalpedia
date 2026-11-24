-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanPairStationaryIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:45:12.816368+00:00
-- url     : https://prove2.me/submissions/068156bb-12b6-4d28-ad77-9e9720ec0493

import Theorems.Thm_Kyprianou_Ch02_identDistribPairOfAELimitsV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanGridIncrementTendstoV1
import Theorems.Thm_Kyprianou_Ch02_levyJordanGridStationaryLawV1
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
    ProbabilityTheory.HasStationaryIncrements
      (fun t ω => (Spos t ω, Sneg t ω)) P := by
  dsimp only
  intro s u
  have h := Kyprianou.Ch02.bvLevyJordanGridIncrementTendstoV1 P X hX hBV
  exact Kyprianou.Ch02.identDistribPairOfAELimitsV1 P _ _ _ _
    (fun n => Kyprianou.Ch02.levyJordanGridStationaryLawV1 P X hX n s u)
    (h s (s+u) (by simp)) (h 0 u (by positivity))
