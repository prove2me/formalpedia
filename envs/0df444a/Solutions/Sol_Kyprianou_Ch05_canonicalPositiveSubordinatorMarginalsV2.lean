-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositiveSubordinatorMarginalsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:42:18.974949+00:00
-- url     : https://prove2.me/submissions/8d913761-6dc1-479a-988e-acb16ee0a9b4

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorRealLaplaceAnchorV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonStationaryIncrementsV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCadlagMonotoneV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorComplexCharacteristicRawV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCharFunV1
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
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    IsLevyProcess X Q ∧ ∀ t : NNReal, P.map (Y t) = Q.map (X t) := by
  classical
  dsimp only
  obtain ⟨hi,_⟩ := killedSubordinatorRealLaplaceAnchorV1 P Y death eta d Pi Phi
    hKilled hTriplet hLaplaceLaw
  have hs : ∀ᵐ z ∂Pi, z ∈ Ioi (0 : ℝ) := by
    rw [ae_iff]
    have he : {z : ℝ | ¬ z ∈ Ioi (0 : ℝ)} = Iic 0 := by
      ext z
      simp only [mem_setOf_eq,mem_Ioi,mem_Iic,not_lt]
    rw [he]
    exact hTriplet.2.2.1
  rw [Measure.restrict_eq_self_of_ae_mem hs] at hi
  refine ⟨⟨?_,canonicalPositivePoissonIndependentIncrementsV1 Q Pi K Z hd hi d,
    canonicalPositivePoissonStationaryIncrementsV1 Q Pi K Z hd hi d,?_⟩,?_⟩
  · funext w
    simp
  · filter_upwards [canonicalPositivePoissonCadlagMonotoneV1 Q Pi K Z hd hi d
      hTriplet.2.1] with w hw
    exact hw.2
  · intro t
    have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1 t
    have hq := (positivePoissonStripMeasurableAmbientV1 Q Pi K Z hd hi 0 t).const_add (d*(t : ℝ))
    letI : IsProbabilityMeasure (P.map (Y t)) := Measure.isProbabilityMeasure_map hm
    letI : IsProbabilityMeasure (Q.map (fun w => d*(t : ℝ) +
      (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal)) :=
      Measure.isProbabilityMeasure_map hq.aemeasurable
    apply Measure.ext_of_charFun
    funext u
    exact (killedSubordinatorComplexCharacteristicRawV1 P Y death eta d Pi Phi
      hKilled hTriplet hLaplaceLaw t u).trans
      (canonicalPositivePoissonCharFunV1 Q Pi K Z hd hi d t u).symm
