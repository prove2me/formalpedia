-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanIndependentPathsV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:04:38.018729+00:00
-- url     : https://prove2.me/submissions/99bdf303-b9bd-4365-9912-dfe1eb578630
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPairStationaryIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPairIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanTimeIndependenceV1
import Theorems.Thm_Kyprianou_Ch02_indepFunToFinTwoV1
import Theorems.Thm_Kyprianou_Ch02_jointLevyPairIndependentPathsOfMarginalIndependenceV1
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
    ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then Spos t ω else Sneg t ω) P := by
  dsimp only
  let V (t : ℝ≥0) (ω : Ω) := variationOnFromTo (fun s => X s ω) Set.univ 0 t
  let A (t : ℝ≥0) (ω : Ω) := (V t ω + X t ω)/2
  let B (t : ℝ≥0) (ω : Ω) := (V t ω - X t ω)/2
  obtain ⟨hA,hB⟩ := Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1 P X hX hBV
  have h := Kyprianou.Ch02.jointLevyPairIndependentPathsOfMarginalIndependenceV1
    P A B hA.start_zero hB.start_zero
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P A hA)
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P B hB)
    (Kyprianou.Ch02.bvLevyCanonicalJordanPairIndependentIncrementsV1 P X hX hBV)
    (Kyprianou.Ch02.bvLevyCanonicalJordanPairStationaryIncrementsV1 P X hX hBV)
    (Kyprianou.Ch02.bvLevyCanonicalJordanTimeIndependenceV1 P X hX hBV)
  convert Kyprianou.Ch02.indepFunToFinTwoV1 P _ _ h using 1
  funext i ω t
  by_cases hi : i=0 <;> simp [hi,A,B,V]
