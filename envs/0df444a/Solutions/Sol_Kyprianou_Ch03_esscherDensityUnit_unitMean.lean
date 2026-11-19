-- Prove2me | solution 1 for Kyprianou.Ch03.esscherDensityUnit_unitMean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:52:10.074581+00:00
-- url     : https://prove2.me/submissions/a999666f-1dac-438c-b304-37991c43b13b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Theorems.Thm_Kyprianou_Ch03_esscherDensity_densityTimeConsistency
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)
    (∀ t : NNReal,
(∫ omega, esscherDensity X beta k t omega ∂P) = 1) := by
  let k : ℝ := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)
  change ∀ t : NNReal, (∫ omega, esscherDensity X beta k t omega ∂P) = 1
  refine fun t => ?_
  have hSource :=
    Kyprianou.Ch03.esscherDensity_densityTimeConsistency
      P F X hX hNatural T hLK beta hBeta
  have hIndicator :=
    hSource 0 t (show (0 : NNReal) ≤ t from zero_le)
      Set.univ (by simp)
  have hEquality :
      (∫ omega, esscherDensity X beta k t omega ∂P) =
      (∫ omega, esscherDensity X beta k 0 omega ∂P) := by
    simpa using hIndicator
  have hZero (omega : Omega) : X 0 omega = 0 :=
    congrFun hX.start_zero omega
  simpa [esscherDensity, hZero] using hEquality
