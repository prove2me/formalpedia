-- Prove2me | solution 1 for Kyprianou.Ch03.esscherCanonicalRawDensityConsistencyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:15:53.301423+00:00
-- url     : https://prove2.me/submissions/9039c1da-10c0-4dbd-ac87-b1e2496867be

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_expMoment_reverse
import Theorems.Thm_Kyprianou_Ch03_rawEsscherUnitFromMomentsV1
import Theorems.Thm_Kyprianou_Ch03_rawEsscherPastFactorV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    (P : Measure {path : NNReal → ℝ // path 0 = 0}) [IsProbabilityMeasure P]
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t omega, X t omega = omega.val t)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)
    (∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1) ∧
    (∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)) := by
  let k := Real.log (∫ w, Real.exp (beta * X 1 w) ∂P)
  have hm (u : NNReal) : Measurable (X u) := by
    have he : X u = fun w : {path : NNReal → ℝ // path 0 = 0} => w.val u := funext (hCoordinate u)
    rw [he]
    exact (measurable_pi_apply u).comp measurable_subtype_coe
  have hi := Kyprianou.Ch03.expMoment_reverse P X hX T hLK beta hBeta
  have hu := Kyprianou.Ch03.rawEsscherUnitFromMomentsV1 P X hX beta hi
  exact ⟨hu, Kyprianou.Ch03.rawEsscherPastFactorV1 P X hX beta hm k hu⟩
