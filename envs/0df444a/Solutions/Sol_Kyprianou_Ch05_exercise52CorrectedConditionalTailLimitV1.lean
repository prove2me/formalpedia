-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CorrectedConditionalTailLimitV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jakevej
-- created : 2026-11-27T02:28:10.944866+00:00
-- url     : https://prove2.me/submissions/d189b587-9c1d-4fe5-a8ad-754ff6b49277
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailProbabilityV1
import Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailSupportV1
import Theorems.Thm_Kyprianou_Ch05_exercise52IntegratedTailFiniteMeanV1
import Theorems.Thm_Kyprianou_Ch05_exercise52CompoundPoissonTailLimitV1
import Theorems.Thm_Kyprianou_Ch05_exercise52CorrectedYToXLimitTransferV1
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
       (Set.Ioi 0) volume) → ∀ u y : Real, 0 < u → 0 < y →
      Tendsto
        (fun x : Real =>
          conditionalRunningSupremumPair P Y
            (fun _ => (⊤ : WithTop NNReal)) x
            (Set.Ioi u) (Set.Ioi y))
        atTop
        (nhds
          ((∫ z in Set.Ioi (u+y),
              (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F))) := by
  intro hInt u y hu hy
  have hP : IsProbabilityMeasure F := by
    rw [hJumpLaw]
    exact exercise52IntegratedTailProbabilityV1 triplet.levyMeasure m hMPositive hM
  have hS := exercise52IntegratedTailSupportV1 triplet.levyMeasure m
    (by rw [← hJumpLaw]; exact hP)
  have hI := exercise52IntegratedTailFiniteMeanV1 triplet.levyMeasure m hMPositive hInt
  rw [← hJumpLaw] at hS hI
  letI : IsProbabilityMeasure F := hP
  have hXlim := exercise52CompoundPoissonTailLimitV1 P X Xleft deathX F hS.1 hS.2 hI
    hX hXCompoundPoisson hLeftX u y hu hy
  have hTr := exercise52CorrectedYToXLimitTransferV1
    P Y X Xleft triplet hLevy hLK hBV hPositiveJumps hDownwardDrift
    m hM hMPositive F hJumpLaw deathX hX hXCompoundPoisson hLeftX hInt u y hu hy
  simpa only [sub_add_cancel, zero_add] using Tendsto.add hTr hXlim
