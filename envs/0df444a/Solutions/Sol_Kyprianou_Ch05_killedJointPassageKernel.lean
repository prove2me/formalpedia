-- Prove2me | solution 1 for Kyprianou.Ch05.killedJointPassageKernel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:04:31.514382+00:00
-- url     : https://prove2.me/submissions/615a8c30-f170-488d-ab67-5d2c0e505c37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorPositiveLevyMeasureV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositiveSubordinatorMarginalsV2
import Theorems.Thm_Kyprianou_Ch05_killedPassageDiscountedPathFunctionalV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingIntegralV2
import Theorems.Thm_Kyprianou_Ch05_killedPotentialOccupationKernelV1
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfMarginalLawsV1
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorRealLaplaceAnchorV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  ∀ (x : Real), 0 < x →
    ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
      A ⊆ Set.Ioi (0 : Real) → B ⊆ Set.Icc (0 : Real) x →
        positiveJointPassageLaw P Y Yleft death x A B =
          jumpPotentialKernel (U 0) Pi x A B
 := by
  intro x hx A B hA hB hAp hBp
  have hnu := killedSubordinatorPositiveLevyMeasureV1 eta d Pi Phi hTriplet
  letI : SigmaFinite Pi := hnu.sigmaFinite
  obtain ⟨Lambda,m,Q,K,Z,hQ,hd⟩ := ProbabilityTheory.exists_isPoissonPointFamily
    ((volume : Measure ℝ).prod Pi)
  letI : MeasurableSpace Lambda := m
  letI : IsProbabilityMeasure Q := hQ
  let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  obtain ⟨hX,hMarg⟩ := canonicalPositiveSubordinatorMarginalsV2
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw Q K Z hd
  have hPath := Kyprianou.Ch02.levyWholePathLawEqOfMarginalLawsV1
    P Q Y X hKilled.1.1 hX hMarg
  have hi := (killedSubordinatorRealLaplaceAnchorV1 P Y death eta d Pi Phi
    hKilled hTriplet hLaplaceLaw).1
  have hres : Pi.restrict (Ioi (0 : ℝ)) = Pi := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply ae_iff.mpr
    have hs : {z : ℝ | ¬ z ∈ Ioi (0 : ℝ)} = Iic 0 := by ext z; simp
    rw [hs]
    exact hTriplet.2.2.1
  rw [hres] at hi
  obtain ⟨H,hHm,hEvent,hH⟩ := killedPassageDiscountedPathFunctionalV1
    P Y Yleft death eta d Pi Phi hKilled hLeft x hx A B hA hB hAp hBp
  rw [hEvent,hPath]
  rw [canonicalPositivePoissonCrossingIntegralV2 Q Pi K Z hd eta d
    hTriplet.1 hTriplet.2.1 hTriplet.2.2.1 hi x hx A B hA hB hAp hBp H hHm hH]
  rw [killedPotentialOccupationKernelV1 P Y death eta d Pi Phi hKilled hTriplet
    hLaplaceLaw U hPotential x hx A B hA hB hAp hBp]
  apply lintegral_congr
  intro t
  rw [hMarg (Real.toNNReal t)]
