-- Prove2me | solution 1 for Kyprianou.Ch03.esscherChangeOfMeasurePreservesLevyAndTriplet
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:12:59.573423+00:00
-- url     : https://prove2.me/submissions/ba7e7791-6e0e-4e86-b721-d17b6944f392
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_esscherTripletWitness_constructed
import Theorems.Thm_Kyprianou_Ch03_esscherTripletWitness_property1
import Theorems.Thm_Kyprianou_Ch03_esscherTripletWitness_property2
import Theorems.Thm_Kyprianou_Ch03_esscherTripletWitness_property3
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P)) :
    exists (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧
      Tbeta.gaussianVariance = T.gaussianVariance ∧
      Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧
      ProbabilityTheory.IsLevyProcess X Q ∧
      (forall (t : NNReal) (xi : Real),
        charFun (Q.map (X t)) xi =
          Complex.exp ((((t : Real) : Complex)) *
            Kyprianou.Ch01.levyTripleExponent Tbeta xi)) ∧
      (forall theta : Real,
        Integrable (fun omega => Real.exp ((theta + beta) * X 1 omega)) P ->
        Real.log (∫ omega, Real.exp (theta * X 1 omega) ∂Q) =
          Real.log
            (∫ omega, Real.exp ((theta + beta) * X 1 omega) ∂P) -
          Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)) := by
  rcases Kyprianou.Ch03.esscherTripletWitness_constructed P Q F X hX hNatural T hLK beta hBeta hEsscher with ⟨Tbeta, h1, h2, h3⟩
  have hparams : (Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧ Tbeta.gaussianVariance = T.gaussianVariance ∧ Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x)))) := ⟨h1, h2, h3⟩
  refine ⟨Tbeta, h1, h2, h3, ?_, ?_, ?_⟩
  · exact Kyprianou.Ch03.esscherTripletWitness_property1 P Q F X hX hNatural T hLK beta hBeta hEsscher Tbeta hparams
  · exact Kyprianou.Ch03.esscherTripletWitness_property2 P Q F X hX hNatural T hLK beta hBeta hEsscher Tbeta hparams
  · exact Kyprianou.Ch03.esscherTripletWitness_property3 P Q F X hX hNatural T hLK beta hBeta hEsscher Tbeta hparams


