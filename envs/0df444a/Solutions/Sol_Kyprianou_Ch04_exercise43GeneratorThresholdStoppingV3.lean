-- Prove2me | solution 1 for Kyprianou.Ch04.exercise43GeneratorThresholdStoppingV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:16:03.604098+00:00
-- url     : https://prove2.me/submissions/f2aa06d0-5e71-4679-8150-030151c2aa96

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_openHitStoppingTimeOfAE
import Theorems.Thm_Kyprianou_Ch04_generatorJumpContinuityOnCompact
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false


open Kyprianou.Ch04

/-- Exercise 4.3(i), with usual filtration and local jump domination. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂triplet.levyMeasure) < ⊤)
    (hNonLattice : triplet.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : Real, 0 < a ∧
        triplet.levyMeasure
          {x : Real | ∃ k : Int, x = (k : Real) * a} =
        triplet.levyMeasure Set.univ)
    (f : Real -> Real) (hf : ContDiff Real 1 f)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (omega : Omega) => Real.exp (-lambda * (t : Real)) * f (X t omega)) F P)
    (hIntegrable : ∀ y : Real,
      Integrable (fun x : Real => f (y + x) - f y)
        triplet.levyMeasure)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b triplet.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂triplet.levyMeasure, ‖f (z+x)-f z‖ ≤ b x) :
    ∀ n : Nat,
          let tau : Omega -> WithTop NNReal := fun omega =>
            sInf {v : WithTop NNReal |
              ∃ t : NNReal, v = ↑t ∧
                n < |∫ x : Real,
                   (f (X t omega + x) - f (X t omega))
                   ∂triplet.levyMeasure|}
          ∀ t : NNReal,
            MeasurableSet[(F t)]
              {omega : Omega | tau omega ≤ (t : WithTop NNReal)} := by
  let G := fun y : ℝ => ∫ x, (f (y+x)-f y) ∂triplet.levyMeasure
  have hG : Continuous G := generatorJumpContinuityOnCompact triplet.levyMeasure f hf.continuous hdom
  let Y := fun t w => G (X t w)
  have hY : Adapted F Y := fun t => hG.measurable.comp (hAdapted t)
  have hpath : ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u => Y u w) (Set.Ici t) t := by
    filter_upwards [hLevy.cadlag_ae] with w hw
    intro t
    exact hG.continuousAt.comp_continuousWithinAt (hw t).1
  intro n
  have hB : IsOpen {y : ℝ | (n : ℝ) < |y|} :=
    isOpen_lt continuous_const continuous_abs
  exact openHitStoppingTimeOfAE P F hRC hNull Y hY hpath _ hB
