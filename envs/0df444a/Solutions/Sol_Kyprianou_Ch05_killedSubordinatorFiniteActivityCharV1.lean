-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinatorFiniteActivityCharV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:03:41.974683+00:00
-- url     : https://prove2.me/submissions/cd9a7394-7169-4f43-94f0-c5f74e9059a7

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch02_subordinatorExponentComplexLaplaceAnalyticV1
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorRealLaplaceAnchorV1
import Theorems.Thm_Kyprianou_Ch05_rightHalfPlaneRealAxisUniquenessV1
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 Set Complex
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
    (r : NNReal) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hScale : Pi = (r : ENNReal) • F) :
    ∀ (t : NNReal) (u : ℝ),
      charFun (P.map (Y t)) u =
        Complex.exp ((t : ℝ) * (Complex.I * d * u + r * (charFun F u - 1))) := by
  intro t u
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1 t
  let Q := P.map (Y t)
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hm
  have hQ : Q (Iio (0 : ℝ)) = 0 := by
    rw [show Q = P.map (Y t) from rfl, Measure.map_apply_of_aemeasurable hm measurableSet_Iio]
    have hn : ∀ᵐ w ∂P, 0 ≤ Y t w := by
      filter_upwards [hKilled.1.2] with w hw
      simpa [congrFun hKilled.1.1.start_zero w] using hw (show (0 : NNReal) ≤ t from zero_le)
    have he : Y t ⁻¹' Iio (0 : ℝ) = {w | ¬ 0 ≤ Y t w} := by ext w; simp [not_le]
    rw [he]
    exact ae_iff.mp hn
  obtain ⟨hi,ha⟩ := Kyprianou.Ch05.killedSubordinatorRealLaplaceAnchorV1
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw
  let f : ℂ → ℂ := fun z => ∫ y, Complex.exp (-z * (y : ℂ)) ∂Q
  let g : ℂ → ℂ := fun z => Complex.exp (-((t : ℝ) : ℂ) *
    ((d : ℂ) * z + ∫ y in Ioi (0 : ℝ), (1 - Complex.exp (-z * (y : ℂ))) ∂Pi))
  have hf := Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1 Q hQ
  have hg := Kyprianou.Ch02.subordinatorExponentComplexLaplaceAnalyticV1 Pi hi d hTriplet.2.1 t
  have he := Kyprianou.Ch05.rightHalfPlaneRealAxisUniquenessV1 f g hf.1 hg.1 (ha t)
    (-(u : ℂ) * Complex.I) (by simp)
  have harg (x : ℝ) : -(-(u : ℂ) * Complex.I) * (x : ℂ) =
      (u : ℂ) * (x : ℂ) * Complex.I := by ring
  have hres : Pi.restrict (Ioi (0 : ℝ)) = Pi := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply ae_iff.mpr
    have hs : {x : ℝ | ¬ x ∈ Ioi (0 : ℝ)} = Iic 0 := by ext x; simp
    rw [hs]
    exact hTriplet.2.2.1
  have heq : (∫ x, Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I) ∂F) = charFun F u :=
    (MeasureTheory.charFun_apply_real u).symm
  have hInt : Integrable (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)) F := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun x => by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im]
  have hJ : (∫ y in Ioi (0 : ℝ), (1 - Complex.exp (-(-(u : ℂ) * Complex.I) * (y : ℂ))) ∂Pi) =
      (r : ℂ) * (1 - charFun F u) := by
    rw [hres,hScale,integral_smul_measure]
    simp_rw [harg]
    rw [integral_sub (integrable_const _) hInt,heq]
    simp [smul_eq_mul,Algebra.smul_def]
  change charFun Q u = _
  rw [MeasureTheory.charFun_apply_real]
  change (∫ x, Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I) ∂Q) = _
  change (∫ x, Complex.exp (-(-(u : ℂ) * Complex.I) * (x : ℂ)) ∂Q) = _ at he
  simp_rw [harg] at he
  change _ = g (-(u : ℂ) * Complex.I) at he
  rw [he]
  dsimp [g]
  rw [hJ]
  congr 1
  ring
