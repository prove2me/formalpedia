-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinatorComplexCharacteristicRawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:42:20.016926+00:00
-- url     : https://prove2.me/submissions/59281eca-9be7-4b59-b969-04e9b4c8e172

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorExponentComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch05_rightHalfPlaneRealAxisUniquenessV1
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
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (t : NNReal) (u : ℝ) :
    charFun (P.map (Y t)) u =
      Complex.exp (((t : ℝ) : ℂ) *
        (∫ y in Ioi (0 : ℝ), (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi)
        + ((d*(t : ℝ)*u : ℝ) : ℂ)*Complex.I) := by
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1 t
  let M := P.map (Y t)
  letI : IsProbabilityMeasure M := Measure.isProbabilityMeasure_map hm
  have hM : M (Iio (0 : ℝ)) = 0 := by
    rw [show M = P.map (Y t) from rfl, Measure.map_apply_of_aemeasurable hm measurableSet_Iio]
    have hn : ∀ᵐ w ∂P, 0 ≤ Y t w := by
      filter_upwards [hKilled.1.2] with w hw
      have hh := hw (show (0 : NNReal) ≤ t from zero_le)
      simpa [congrFun hKilled.1.1.start_zero w] using hh
    simpa only [Set.preimage,Set.mem_Iio,not_le] using ae_iff.mp hn
  obtain ⟨hi,ha⟩ := killedSubordinatorRealLaplaceAnchorV1
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw
  let f : ℂ → ℂ := fun z => ∫ y, Complex.exp (-z * (y : ℂ)) ∂M
  let g : ℂ → ℂ := fun z => Complex.exp (-((t : ℝ) : ℂ) *
    ((d : ℂ) * z + ∫ y in Ioi (0 : ℝ), (1 - Complex.exp (-z * (y : ℂ))) ∂Pi))
  have hf := Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1 M hM
  have hg := Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1 Pi hi d hTriplet.2.1 t
  have he := rightHalfPlaneRealAxisUniquenessV1 f g hf.1 hg.1 (ha t)
    (-(u : ℂ) * Complex.I) (by simp)
  dsimp [f,g] at he
  rw [charFun_apply_real]
  have hleft : (fun y : ℝ => Complex.exp ((u : ℂ)*(y : ℂ)*Complex.I)) =
      fun y : ℝ => Complex.exp (-(-(u : ℂ)*Complex.I)*(y : ℂ)) := by
    funext y
    congr 1
    ring
  rw [hleft,he]
  have hr : (fun y : ℝ => 1 - Complex.exp (-(-(u : ℂ)*Complex.I)*(y : ℂ))) =
      fun y => -(Complex.exp (Complex.I*((u*y : ℝ) : ℂ))-1) := by
    funext y
    have h : -(-(u : ℂ)*Complex.I)*(y : ℂ) = Complex.I*((u*y : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h]
    ring
  rw [hr,integral_neg]
  congr 1
  push_cast
  ring
