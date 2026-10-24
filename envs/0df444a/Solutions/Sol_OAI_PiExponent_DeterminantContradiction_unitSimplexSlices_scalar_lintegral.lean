-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlices_scalar_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:17:04.289836+00:00
-- url     : https://prove2.me/submissions/236b7649-ed98-46a0-96ed-5f0611555cc6

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

theorem solution (n : Nat) (c : ENNReal) :
    (∫⁻ t : Real,
      (if t ∈ Set.Icc (0 : Real) 1 then
        c * ENNReal.ofReal ((1 - t) ^ n)
      else 0) ∂MeasureTheory.volume) =
      c * ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  let g : Real → Real := fun t => (1 - t) ^ n
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hgmeas : Measurable fun t : Real => ENNReal.ofReal (g t) := by
    exact ENNReal.continuous_ofReal.measurable.comp hg.measurable
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : Real) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_nonneg (sub_nonneg.mpr ht.2) n
  have hint : Integrable g (volume.restrict (Set.Icc (0 : Real) 1)) := by
    exact hg.locallyIntegrable.integrableOn_isCompact isCompact_Icc
  have hinterval :
      (∫ t, g t ∂(volume.restrict (Set.Icc (0 : Real) 1))) =
        ∫ t in (0 : Real)..1, g t := by
    calc
      (∫ t, g t ∂(volume.restrict (Set.Icc (0 : Real) 1))) =
          ∫ t in Set.Icc (0 : Real) 1, g t ∂volume := rfl
      _ = ∫ t in Set.Ioc (0 : Real) 1, g t ∂volume :=
        integral_Icc_eq_integral_Ioc
      _ = ∫ t in (0 : Real)..1, g t :=
        (intervalIntegral.integral_of_le (μ := volume) (by norm_num : (0 : Real) ≤ 1)).symm
  have hconvert :
      (∫⁻ t in Set.Icc (0 : Real) 1, ENNReal.ofReal (g t)) =
        ENNReal.ofReal (∫ t in (0 : Real)..1, g t) := by
    calc
      (∫⁻ t in Set.Icc (0 : Real) 1, ENNReal.ofReal (g t)) =
          ENNReal.ofReal (∫ t, g t ∂(volume.restrict (Set.Icc (0 : Real) 1))) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
      _ = ENNReal.ofReal (∫ t in (0 : Real)..1, g t) := by rw [hinterval]
  have hfun :
      (fun t : Real => if t ∈ Set.Icc (0 : Real) 1 then
        c * ENNReal.ofReal (g t) else 0) =
        Set.indicator (Set.Icc (0 : Real) 1)
          (fun t => c * ENNReal.ofReal (g t)) := by
    funext t
    by_cases ht : t ∈ Set.Icc (0 : Real) 1 <;> simp [ht]
  rw [hfun, lintegral_indicator measurableSet_Icc,
    lintegral_const_mul'' c hgmeas.aemeasurable, hconvert]