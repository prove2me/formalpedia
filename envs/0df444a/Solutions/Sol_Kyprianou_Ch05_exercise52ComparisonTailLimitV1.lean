-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52ComparisonTailLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:40.116737+00:00
-- url     : https://prove2.me/submissions/46bbb3bf-6ec3-4365-b844-180256a4a1b1

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailProbabilityV1
import Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailSupportV1
import Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailFiniteMeanV1
import Theorems.Thm_Kyprianou_Ch05_exercise52CompoundPoissonTailLimitV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y X Xleft : NNReal → Omega → Real)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hLevy : ProbabilityTheory.IsLevyProcess Y P)
    (hLK : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (Y t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
       (∫⁻ z in Set.Ioo (-1 : Real) 1,
         ENNReal.ofReal |z| ∂triplet.levyMeasure) < ⊤)
    (hPositiveJumps : triplet.levyMeasure (Set.Iio 0) = 0)
    (hDownwardDrift : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => Y t omega) atTop atBot)
    (m : Real)
    (hM : m =
       ∫ z in Set.Ioi (0 : Real),
         (triplet.levyMeasure (Set.Ioi z)).toReal ∂volume)
    (hMPositive : 0 < m)
    (F : Measure Real)
    (hJumpLaw : F = ascendingRecordJumpDistribution
      triplet.levyMeasure m)
    (deathX : Omega → WithTop NNReal)
    (hX : IsKilledSubordinator P X deathX 0)
    (hXCompoundPoisson : ∀ (t : NNReal) (theta : Real),
        0 ≤ theta →
          (∫ omega, Real.exp (-theta*X t omega) ∂P) =
            Real.exp (-(t : Real) *
              (∫ z in Set.Ioi 0,
                (1-Real.exp (-theta*z)) ∂F)))
    (hLeftX : IsLeftLimitVersion P X Xleft)
    :
  (IntegrableOn
       (fun z : Real => z * (triplet.levyMeasure (Set.Ioi z)).toReal)
       (Set.Ioi 0) volume) →
    ∀ u y : Real, 0 < u → 0 < y →
      Tendsto
        (fun x : Real =>
          (P {omega : Omega |
          PassageFinite X deathX x omega ∧
          passageOvershoot X deathX x omega ∈ Set.Ioi u ∧
          passageUndershoot X Xleft deathX x omega ∈ Set.Ioi y}).toReal)
        atTop
        (nhds
          ((∫ z in Set.Ioi (u+y),
              (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F))) := by
  intro hInt
  have hP : IsProbabilityMeasure F := by
    rw [hJumpLaw]
    exact exercise52IntegratedTailProbabilityV1 triplet.levyMeasure m hMPositive hM
  have hS := exercise52IntegratedTailSupportV1 triplet.levyMeasure m
    (by rw [← hJumpLaw]; exact hP)
  have hI := exercise52IntegratedTailFiniteMeanV1 triplet.levyMeasure m hMPositive hInt
  rw [← hJumpLaw] at hS hI
  letI : IsProbabilityMeasure F := hP
  exact exercise52CompoundPoissonTailLimitV1 P X Xleft deathX F hS.1 hS.2 hI
    hX hXCompoundPoisson hLeftX



