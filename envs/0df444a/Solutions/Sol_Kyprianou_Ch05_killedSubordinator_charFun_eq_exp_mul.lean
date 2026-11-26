-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_charFun_eq_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:01:34.407522+00:00
-- url     : https://prove2.me/submissions/d8d498c7-7ea4-484a-8da5-84345ea577b5

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorExponentComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch05_rightHalfPlaneRealAxisUniquenessV1
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorRealLaplaceAnchorV1
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorImaginaryBoundaryExpansionV1
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Complex
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
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  ∀ (t : NNReal) (u : Real),
    MeasureTheory.charFun (P.map (Y t)) u =
      Complex.exp (↑(-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) +
        ↑((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u)) * Complex.I)
  := by
  intro t u
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1 t
  let Q := P.map (Y t)
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hm
  have hQ : Q (Set.Iio (0 : ℝ)) = 0 := by
    rw [show Q = P.map (Y t) from rfl, Measure.map_apply_of_aemeasurable hm measurableSet_Iio]
    have hn : ∀ᵐ w ∂P, 0 ≤ Y t w := by
      filter_upwards [hKilled.1.2] with w hw
      have hh := hw (show (0 : NNReal) ≤ t from zero_le)
      simpa [congrFun hKilled.1.1.start_zero w] using hh
    have he : Y t ⁻¹' Set.Iio (0 : ℝ) = {w | ¬ 0 ≤ Y t w} := by
      ext w
      simp [not_le]
    rw [he]
    exact ae_iff.mp hn
  obtain ⟨hi,ha⟩ := Kyprianou.Ch05.killedSubordinatorRealLaplaceAnchorV1
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw
  let f : ℂ → ℂ := fun z => ∫ y, Complex.exp (-z * (y : ℂ)) ∂Q
  let g : ℂ → ℂ := fun z => Complex.exp (-((t : ℝ) : ℂ) *
    ((d : ℂ) * z + ∫ y in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (y : ℂ))) ∂Pi))
  have hf := Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1 Q hQ
  have hg := Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1 Pi hi d hTriplet.2.1 t
  have he := Kyprianou.Ch05.rightHalfPlaneRealAxisUniquenessV1 f g hf.1 hg.1 (ha t)
    (-(u : ℂ) * Complex.I) (by simp)
  exact Kyprianou.Ch05.killedSubordinatorImaginaryBoundaryExpansionV1 Q Pi hi d t u he
