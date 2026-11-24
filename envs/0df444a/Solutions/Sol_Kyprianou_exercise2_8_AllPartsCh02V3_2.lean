-- Prove2me | solution 2 for Kyprianou.exercise2_8_AllPartsCh02V3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:16:40.551192+00:00
-- url     : https://prove2.me/submissions/2b182339-b93e-49bb-bbcc-7fe85aeecb44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanIndependentPathsV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    ∃ (Spos Sneg : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess Spos P ∧
      ProbabilityTheory.IsLevyProcess Sneg P ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Spos t ω)) ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Sneg t ω)) ∧
      ProbabilityTheory.iIndepFun
        (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
           if i = 0 then Spos t ω else Sneg t ω) P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω)
      := by
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
  obtain ⟨hp, hn, heq⟩ := Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1 P X hX hBV
  obtain ⟨hLp, hLn⟩ := Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1 P X hX hBV
  exact ⟨Spos, Sneg, hLp, hLn, hp, hn,
    Kyprianou.Ch02.bvLevyCanonicalJordanIndependentPathsV1 P X hX hBV, heq⟩

