-- Prove2me | solution 1 for Kyprianou.Ch04.boundedVariationChangeOfVariables
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:55:41.784386+00:00
-- url     : https://prove2.me/submissions/f64413a4-2b3b-40c4-a880-51025110cceb

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_bvActualJumpDriftRepresentationV1
import Theorems.Thm_Kyprianou_Ch04_bvDeterministicJumpChainRuleV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (Xleft : NNReal → Omega → Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      0 < t →
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      f ((t : Real), X t omega) =
        f (0, X 0 omega) +
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (s, X (Real.toNNReal s) omega)
            (1, 0) ∂volume) +
        (triplet.drift -
          ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure) *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            fderiv Real f (s, X (Real.toNNReal s) omega)
              (0, 1) ∂volume) +
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega))
          ∂(pathJumpMeasure X Xleft omega)) := by
  filter_upwards [hLevy.cadlag_ae, hLeft,
    bvActualJumpDriftRepresentationV1 P X hLevy triplet hTriplet hBV Xleft hLeft]
    with omega hCadlag hLeftPath hRep
  exact bvDeterministicJumpChainRuleV1 X Xleft omega
    (triplet.drift - ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    hCadlag hLeftPath hRep f hf
