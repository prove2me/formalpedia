-- Prove2me | solution 1 for Kyprianou.Ch03.esscherDensityUnit_integrability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:51:56.797018+00:00
-- url     : https://prove2.me/submissions/190a3d04-3177-4140-9480-3f8da8962a7b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Theorems.Thm_Kyprianou_Ch03_esscherDensityUnit_unitMean
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
Integrable (esscherDensity X beta k t) P) := by
  let k : ℝ := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)
  change ∀ t : NNReal, Integrable (esscherDensity X beta k t) P
  refine fun t => ?_
  have hnonzero :
      (∫ omega, esscherDensity X beta k t omega ∂P) ≠ 0 := by
    rw [Kyprianou.Ch03.esscherDensityUnit_unitMean
      P F X hX hNatural T hLK beta hBeta t]
    norm_num
  exact MeasureTheory.Integrable.of_integral_ne_zero hnonzero
