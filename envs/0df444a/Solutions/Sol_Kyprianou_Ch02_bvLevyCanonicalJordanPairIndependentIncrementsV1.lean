-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanPairIndependentIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:47:26.111576+00:00
-- url     : https://prove2.me/submissions/1b3fe5b5-1e52-4a96-b128-0d7d4f5c2aed

import Theorems.Thm_Kyprianou_Ch02_iIndepFunPairOfAELimitsV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanGridIncrementTendstoV1
import Theorems.Thm_Kyprianou_Ch02_levyJordanGridBlockIndependenceV1
import Theorems.Thm_Kyprianou_Ch02_levyJordanGridPairAEMeasurableV1
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
    ProbabilityTheory.HasIndependentIncrements
      (fun t ω => (Spos t ω, Sneg t ω)) P := by
  dsimp only
  intro m t ht
  have h := Kyprianou.Ch02.bvLevyJordanGridIncrementTendstoV1 P X hX hBV
  exact Kyprianou.Ch02.iIndepFunPairOfAELimitsV1 P m _ _
    (fun n i => Kyprianou.Ch02.levyJordanGridPairAEMeasurableV1
      P X hX n (t i.castSucc) (t i.succ))
    (fun n => Kyprianou.Ch02.levyJordanGridBlockIndependenceV1 P X hX n m t ht)
    (fun i => h (t i.castSucc) (t i.succ) (ht (by exact Fin.castSucc_le_succ i)))
