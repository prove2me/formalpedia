-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52SpectrallyPositiveRiskJointLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:17:50.319369+00:00
-- url     : https://prove2.me/submissions/7ded9bdb-9234-4127-adae-5b24da3c2962
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52ConditionalRiskComparisonV1
import Theorems.Thm_Kyprianou_Ch05_exercise52ComparisonTailLimitV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Exercise 5.2, all three source parts: risk process,
conditional joint law, limiting law and reserve/deficit interpretation. -/
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
    (hMPositive : 0 < m) (F : Measure Real)
    (hJumpLaw : F = ascendingRecordJumpDistribution triplet.levyMeasure m)
    (deathX : Omega → WithTop NNReal) (hX : IsKilledSubordinator P X deathX 0)
    (hXCompoundPoisson : ∀ (t : NNReal) (theta : Real),
        0 ≤ theta →
          (∫ omega, Real.exp (-theta*X t omega) ∂P) =
            Real.exp (-(t : Real) *
              (∫ z in Set.Ioi 0,
                (1-Real.exp (-theta*z)) ∂F)))
    (hLeftX : IsLeftLimitVersion P X Xleft) :
   let hFiniteSecondMoment : Prop := IntegrableOn
       (fun z : Real => z * (triplet.levyMeasure (Set.Ioi z)).toReal)
       (Set.Ioi 0) volume;
    -- (i) Conditional equality of the entire joint passage law,
   -- with no assumed target equality between the two processes.
   -- Source-implied positive risk passage and almost-sure comparison passage.
   ((∀ x : Real, 0 < x →
      0 < (P {omega : Omega |
        PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal ∧
      (P {omega : Omega | PassageFinite X deathX x omega}).toReal = 1) ∧
    -- (i) Source-exact conditional risk law equals unconditioned comparison law.
    (∀ x : Real, 0 < x →
      ∀ A B : Set Real, MeasurableSet A → MeasurableSet B →
        conditionalRunningSupremumPair P Y
          (fun _ => (⊤ : WithTop NNReal)) x A B =
        (P {omega : Omega |
          PassageFinite X deathX x omega ∧
          passageOvershoot X deathX x omega ∈ A ∧
          passageUndershoot X Xleft deathX x omega ∈ B}).toReal) ∧
    -- (ii) The full finite-mean limiting joint overshoot and undershoot.
    (hFiniteSecondMoment → ∀ u y : Real, 0 < u → 0 < y →
      Tendsto
        (fun x : Real =>
          conditionalRunningSupremumPair P Y
            (fun _ => (⊤ : WithTop NNReal)) x
            (Set.Ioi u) (Set.Ioi y))
        atTop
        (nhds
          ((∫ z in Set.Ioi (u+y),
              (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F)))) ∧
    -- (iii) Historical minimum reserve, based on the running maximum of Y,
    -- distinguished from the current pre-ruin reserve.
    (hFiniteSecondMoment → ∀ deficit wealth : Real, 0 < deficit → 0 < wealth →
      Tendsto
        (fun capital : Real =>
          (P {omega : Omega |
             PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) capital omega ∧
             deficit <
               Y (passageFiniteTime Y
                   (fun _ => (⊤ : WithTop NNReal)) capital omega) omega -
                 capital ∧
             wealth <
               capital - runningSupremumBefore Y (passageFiniteTime Y
                 (fun _ => (⊤ : WithTop NNReal)) capital omega) omega}).toReal /
          (P {omega : Omega |
             PassageFinite Y
               (fun _ => (⊤ : WithTop NNReal)) capital omega}).toReal)
        atTop
        (nhds
           ((∫ z in Set.Ioi (deficit+wealth),
               (F (Set.Ioi z)).toReal ∂volume) /
               (∫ z : Real, z ∂F)))))
 := by
  dsimp only
  obtain ⟨hPass, hLaw⟩ := exercise52ConditionalRiskComparisonV1
    P Y X Xleft triplet hLevy hLK hBV hPositiveJumps hDownwardDrift
    m hM hMPositive F hJumpLaw deathX hX hXCompoundPoisson hLeftX
  have hLimit : IntegrableOn
       (fun z : Real => z * (triplet.levyMeasure (Set.Ioi z)).toReal)
       (Set.Ioi 0) volume → ∀ u y : ℝ, 0 < u → 0 < y →
      Tendsto (fun x : ℝ => conditionalRunningSupremumPair P Y
          (fun _ => (⊤ : WithTop NNReal)) x (Set.Ioi u) (Set.Ioi y))
        atTop (nhds ((∫ z in Set.Ioi (u+y), (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : ℝ, z ∂F))) := by
    intro h u y hu hy
    have hlim := exercise52ComparisonTailLimitV1
      P Y X Xleft triplet hLevy hLK hBV hPositiveJumps hDownwardDrift
      m hM hMPositive F hJumpLaw deathX hX hXCompoundPoisson hLeftX h u y hu hy
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (hLaw x hx _ _ measurableSet_Ioi measurableSet_Ioi).symm
  refine ⟨hPass, hLaw, hLimit, ?_⟩
  intro h deficit wealth hd hw
  simpa only [conditionalRunningSupremumPair, passageOvershoot, Set.mem_Ioi] using
    hLimit h deficit wealth hd hw



