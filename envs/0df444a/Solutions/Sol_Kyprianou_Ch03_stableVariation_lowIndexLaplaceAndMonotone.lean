-- Prove2me | solution 1 for Kyprianou.Ch03.stableVariation_lowIndexLaplaceAndMonotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:53.663669+00:00
-- url     : https://prove2.me/submissions/eea8bbd6-cbc8-4921-a274-497f940f8f13

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_levyMonotoneOfNonnegativeMarginalsV1
import Theorems.Thm_Kyprianou_Ch03_stablePositiveNegativeExpIntegrableV1
import Theorems.Thm_Kyprianou_Ch03_stablePositiveLogLaplaceHomogeneityV1
import Theorems.Thm_Kyprianou_Ch03_stablePositiveUnitNonzeroV1
import Theorems.Thm_Kyprianou_Ch03_stableLogLaplaceCoefficientStrictSignV1
import Theorems.Thm_Kyprianou_Ch03_stableNonnegativeOfBoundedNegExpV1
import Theorems.Thm_Kyprianou_Ch03_stableLevyLogMomentTimeScalingV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open scoped Topology
open Kyprianou.Ch03
theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)) :
    (alpha < 1 →
      (∃ C : ℝ, 0 < C ∧
        (∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega,
            Real.exp (-theta * X 1 omega) ∂P) =
              -C * theta ^ alpha)) ∧
      (∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega))) := by
  intro ha
  have hi := Kyprianou.Ch03.stablePositiveNegativeExpIntegrableV1 P X hX T hLK
    alpha c hAlpha hC hGaussian hMeasure hStable
  have hh := Kyprianou.Ch03.stablePositiveLogLaplaceHomogeneityV1 P X hX T hLK
    alpha c hAlpha hC hGaussian hMeasure hStable
  have hn := Kyprianou.Ch03.stablePositiveUnitNonzeroV1 P X hX T hLK
    alpha c hAlpha hC hGaussian hMeasure hStable
  have hs := (Kyprianou.Ch03.stableLogLaplaceCoefficientStrictSignV1 P (X 1)
    alpha hAlpha.1 hn (fun theta htheta => hi theta htheta 1) hh).1 ha
  refine ⟨⟨-Real.log (∫ w, Real.exp (-X 1 w) ∂P), by linarith, ?_⟩, ?_⟩
  · intro theta htheta
    rw [hh theta htheta, neg_neg]
  · apply Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1 P X hX
    intro t
    apply Kyprianou.Ch03.stableNonnegativeOfBoundedNegExpV1 P (X t)
      (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t)
      (fun n => hi n (by positivity) t)
    intro n
    have h := Kyprianou.Ch03.stableLevyLogMomentTimeScalingV1 P X hX (-(n : ℝ))
      (hi n (by positivity)) t
    rw [hh n (by positivity)] at h
    have hpos : 0 < (∫ w, Real.exp (-(n : ℝ) * X t w) ∂P) := by
      apply (integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun w => (Real.exp_pos _).le) (hi n (by positivity) t)).mpr
      have hsupport : Function.support (fun w => Real.exp (-(n : ℝ) * X t w)) = Set.univ := by
        ext w; simp [Function.mem_support, Real.exp_ne_zero]
      rw [hsupport, measure_univ]; norm_num
    apply (Real.log_le_log_iff hpos zero_lt_one).mp
    rw [Real.log_one, h]
    exact mul_nonpos_of_nonneg_of_nonpos t.coe_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hs.le (Real.rpow_nonneg (by positivity) _))
