-- Prove2me | solution 3 for Kyprianou.exercise2_8_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:10:57.192845+00:00
-- url     : https://prove2.me/submissions/79388d82-dfa0-4b12-82f0-76ea3ff06562

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanIndependentPathsV1

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Exercise 2.8 (BV Lévy → independent Jordan subordinators)

Glue sketch reducing `Kyprianou.exercise2_8_AllPartsCh02V3` to the canonical
Jordan variation decomposition on the same probability space:

* `Spos t ω = (V_t(ω) + X_t(ω)) / 2`
* `Sneg t ω = (V_t(ω) - X_t(ω)) / 2`

where `V_t = variationOnFromTo X univ 0 t`.

Already-`Proved` children supply pathwise monotonicity / reconstruction and the
two marginal Lévy properties. The sole remaining open child is path-level
`iIndepFun` of `(Spos, Sneg)`.
-/

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
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω) := by
  -- Canonical Jordan variation processes on (Ω, P).
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
  -- Pathwise monotone Jordan parts + pathwise reconstruction X = Spos - Sneg.
  have hpath :
      (∀ᵐ ω ∂P, Monotone (fun t => Spos t ω)) ∧
      (∀ᵐ ω ∂P, Monotone (fun t => Sneg t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω) :=
    Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1 P X hX hBV
  -- Both Jordan parts are Lévy processes under P.
  have hmarg :
      ProbabilityTheory.IsLevyProcess Spos P ∧
      ProbabilityTheory.IsLevyProcess Sneg P :=
    Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1 P X hX hBV
  -- Path-level independence of the full Jordan processes (open child).
  have hindep :
      ProbabilityTheory.iIndepFun
        (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
          if i = 0 then Spos t ω else Sneg t ω) P :=
    Kyprianou.Ch02.bvLevyCanonicalJordanIndependentPathsV1 P X hX hBV
  exact ⟨Spos, Sneg, hmarg.1, hmarg.2, hpath.1, hpath.2.1, hindep, hpath.2.2⟩
