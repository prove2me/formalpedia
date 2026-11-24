-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanTimeIndependenceV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:28:04.81267+00:00
-- url     : https://prove2.me/submissions/da77c886-515e-4ad0-a5e6-73eff9b2e277
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanTimeLaplaceFactorV1
import Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceFactorIndepFunAEV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
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
    ∀ t : ℝ≥0, ProbabilityTheory.IndepFun (Spos t) (Sneg t) P := by
  dsimp only
  let V (t : ℝ≥0) (ω : Ω) := variationOnFromTo (fun s => X s ω) Set.univ 0 t
  let A (t : ℝ≥0) (ω : Ω) := (V t ω + X t ω)/2
  let B (t : ℝ≥0) (ω : Ω) := (V t ω - X t ω)/2
  obtain ⟨hA,hB⟩ := Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1 P X hX hBV
  obtain ⟨hp,hn,_⟩ := Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1 P X hX hBV
  intro t
  have hpa : ∀ᵐ ω ∂P, 0 ≤ A t ω := by
    filter_upwards [hp] with ω hw
    have h := hw (show (0 : ℝ≥0) ≤ t from zero_le)
    change A 0 ω ≤ A t ω at h
    rwa [show A 0 ω = 0 from congrFun hA.start_zero ω] at h
  have hpb : ∀ᵐ ω ∂P, 0 ≤ B t ω := by
    filter_upwards [hn] with ω hw
    have h := hw (show (0 : ℝ≥0) ≤ t from zero_le)
    change B 0 ω ≤ B t ω at h
    rwa [show B 0 ω = 0 from congrFun hB.start_zero ω] at h
  exact Kyprianou.Ch02.nonnegLaplaceFactorIndepFunAEV1 P (A t) (B t)
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P A hA t)
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P B hB t)
    hpa hpb (Kyprianou.Ch02.bvLevyCanonicalJordanTimeLaplaceFactorV1 P X hX hBV t)
