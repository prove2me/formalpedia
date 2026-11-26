-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinatorImaginaryBoundaryExpansionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:06:12.616804+00:00
-- url     : https://prove2.me/submissions/17154d92-f3be-4f0b-86c4-90744d8b99d4

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_positiveComplexLaplaceKernelIntegrableV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set Complex Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (Q Pi : Measure ℝ) [IsProbabilityMeasure Q]
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|) (Pi.restrict (Ioi (0 : ℝ))))
    (d : ℝ) (t : NNReal) (u : ℝ)
    (h : (∫ y, Complex.exp (-(-(u : ℂ) * Complex.I) * (y : ℂ)) ∂Q) =
      Complex.exp (-((t : ℝ) : ℂ) *
        ((d : ℂ) * (-(u : ℂ) * Complex.I) +
          ∫ y in Ioi (0 : ℝ),
            (1 - Complex.exp (-(-(u : ℂ) * Complex.I) * (y : ℂ))) ∂Pi))) :
    MeasureTheory.charFun Q u =
      Complex.exp (↑(-(t : ℝ) * (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) +
        ↑((t : ℝ) * (∫ x in Ioi (0 : ℝ), Real.sin (u * x) ∂Pi + d * u)) * Complex.I) := by
  let F : ℝ → ℂ := fun x => 1 - Complex.exp (-(-(u : ℂ) * Complex.I) * (x : ℂ))
  have hF : Integrable F (Pi.restrict (Ioi (0 : ℝ))) :=
    Kyprianou.Ch02.positiveComplexLaplaceKernelIntegrableV1 Pi hint
      (-(u : ℂ) * Complex.I) (by simp)
  have harg (x : ℝ) : -(-(u : ℂ) * Complex.I) * (x : ℂ) =
      ((u * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hre (x : ℝ) : (F x).re = 1 - Real.cos (u * x) := by
    simp [F,harg,Complex.exp_re,Complex.mul_re,Complex.mul_im]
  have him (x : ℝ) : (F x).im = -(Real.sin (u * x)) := by
    simp [F,harg,Complex.exp_im,Complex.mul_re,Complex.mul_im]
  have hRe : (∫ x in Ioi (0 : ℝ), F x ∂Pi).re =
      ∫ x in Ioi (0 : ℝ), (1 - Real.cos (u*x)) ∂Pi := by
    change RCLike.re (∫ x in Ioi (0 : ℝ), F x ∂Pi) = _
    rw [← integral_re hF]
    exact integral_congr_ae (ae_of_all _ hre)
  have hIm : (∫ x in Ioi (0 : ℝ), F x ∂Pi).im =
      -(∫ x in Ioi (0 : ℝ), Real.sin (u*x) ∂Pi) := by
    change RCLike.im (∫ x in Ioi (0 : ℝ), F x ∂Pi) = _
    rw [← integral_im hF]
    change (∫ x in Ioi (0 : ℝ), (F x).im ∂Pi) = _
    simp_rw [him]
    exact integral_neg _
  have hCos : Integrable (fun x : ℝ => 1 - Real.cos (u*x)) (Pi.restrict (Ioi 0)) := by
    have hI : Integrable (fun x => (F x).re) (Pi.restrict (Ioi 0)) := hF.re
    simpa only [hre] using hI
  have hCosEq : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (1-Real.cos (u*x)) ∂Pi).toReal =
      ∫ x in Ioi (0 : ℝ), (1 - Real.cos (u*x)) ∂Pi := by
    rw [← ofReal_integral_eq_lintegral_ofReal hCos
      (ae_of_all _ fun x => sub_nonneg.mpr (Real.cos_le_one _))]
    exact ENNReal.toReal_ofReal (integral_nonneg fun x => sub_nonneg.mpr (Real.cos_le_one _))
  have hC : charFun Q u = ∫ y, Complex.exp (-(-(u : ℂ) * Complex.I) * (y : ℂ)) ∂Q := by
    rw [MeasureTheory.charFun_apply_real]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      change Complex.exp ((u : ℂ) * (y : ℂ) * Complex.I) =
        Complex.exp (-(-(u : ℂ) * Complex.I) * (y : ℂ))
      congr 1
      ring
  rw [hC,h]
  congr 1
  change -((t : ℝ) : ℂ) *
      ((d : ℂ) * (-(u : ℂ) * Complex.I) + ∫ x in Ioi (0 : ℝ), F x ∂Pi) = _
  rw [hCosEq]
  apply Complex.ext
  · simp [Complex.mul_re,Complex.mul_im,hRe,hIm]
  · simp [Complex.mul_re,Complex.mul_im,hRe,hIm]
    ring
