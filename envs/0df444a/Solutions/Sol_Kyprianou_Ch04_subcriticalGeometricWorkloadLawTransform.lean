-- Prove2me | solution 1 for Kyprianou.Ch04.subcriticalGeometricWorkloadLawTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:47:01.195028+00:00
-- url     : https://prove2.me/submissions/6d13cf0c-42e6-46c7-8382-e2f0a298df0f

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_trafficIntegratedNegativeTailProbability
import Theorems.Thm_Kyprianou_Ch04_geometricConvolutionNonnegativeSupport
import Theorems.Thm_Kyprianou_Ch04_exercise46GeometricConvolutionLaplaceV2
import Theorems.Thm_Kyprianou_Ch04_integratedNegativeTailLaplaceTransform
import Theorems.Thm_Kyprianou_Ch04_geometricWorkloadResolventArithmetic
import Theorems.Thm_Kyprianou_Ch04_positiveSubcriticalTrafficArithmetic
import Theorems.Thm_Kyprianou_Ch04_bvSubcriticalSecantLower
import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_nonneg
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The geometric workload probability law has nonnegative support and the subcritical Laplace ratio. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    let M := ∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂L.ν
    let rho := M / ENNReal.ofReal L.drift
    let eta := ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun x : ℝ => L.ν (Iio (-x))/(ENNReal.ofReal L.drift*rho))
    let convPow : ℕ → Measure ℝ := Nat.rec (Measure.dirac (0 : ℝ)) (fun _ m => m.conv eta)
    0 < rho → rho < 1 →
    ∀ mu : Measure ℝ, IsProbabilityMeasure mu →
      (∀ B : Set ℝ, MeasurableSet B → mu B = ∑' n : ℕ, ((1-rho)*rho^n) * (convPow n B)) →
      mu (Iio 0) = 0 ∧ ∀ a : ℝ, 0 < a → (∫ x, Real.exp (-a*x) ∂mu) = (L.drift-M.toReal)*a/L.ψ a := by
  intro M rho eta convPow hr0 hr1 mu hmu hLaw
  let : IsProbabilityMeasure eta := Kyprianou.Ch04.trafficIntegratedNegativeTailProbability P F L hBV hd hr0 hr1
  have heta0 : eta (Iio 0) = 0 := by
    apply (withDensity_absolutelyContinuous _ _)
    rw [Measure.restrict_apply measurableSet_Iio]
    simp [Iio_inter_Ioi]
  refine ⟨Kyprianou.Ch04.geometricConvolutionNonnegativeSupport eta mu rho heta0 hLaw, ?_⟩
  intro a ha
  obtain ⟨hMtop,_,hM⟩ := Kyprianou.Ch04.positiveSubcriticalTrafficArithmetic M L.drift hd hr0 hr1
  have hl := Kyprianou.Ch04.bvSubcriticalSecantLower P F L hBV hd hMtop a ha
  have hp : 0 < L.ψ a := by
    have h : 0 < L.ψ a / a := lt_of_lt_of_le (sub_pos.mpr hM) hl
    exact (div_pos_iff.mp h).elim And.left (fun hneg => (not_lt_of_ge ha.le hneg.2).elim)
  have hgap : L.ψ a ≤ L.drift*a := by
    rw [bv_laplace_exponent_positive_magnitude_nonneg L hBV a ha.le]
    apply sub_le_self
    apply integral_nonneg
    intro z
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) z.2))
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le) (by fun_prop)]
  rw [Kyprianou.Ch04.exercise46GeometricConvolutionLaplaceV2 eta mu rho a hLaw,
    show (∫⁻ x, ENNReal.ofReal (Real.exp (-a*x)) ∂eta) = _ from
      Kyprianou.Ch04.integratedNegativeTailLaplaceTransform P F L hBV hd rho a ha]
  rw [Kyprianou.Ch04.geometricWorkloadResolventArithmetic rho L.drift a (L.ψ a) hr0 hr1 hd ha hp hgap]
  have he : L.drift * rho.toReal = M.toReal := by
    change L.drift * (M / ENNReal.ofReal L.drift).toReal = M.toReal
    rw [ENNReal.toReal_div,ENNReal.toReal_ofReal hd.le]
    field_simp [hd.ne']
  rw [he]
