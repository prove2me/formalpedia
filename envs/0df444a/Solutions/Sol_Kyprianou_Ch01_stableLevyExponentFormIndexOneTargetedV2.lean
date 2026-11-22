-- Prove2me | solution 1 for Kyprianou.Ch01.stableLevyExponentFormIndexOneTargetedV2
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T16:57:10.191603+00:00
-- url     : https://prove2.me/submissions/b57a5a66-7220-451e-a49e-c083ff498825

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseAllReal

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

private lemma integral_Iio_zero_eq_Ioi_zero_neg {g : ℝ → ℂ} :
    (∫ x in Set.Iio (0 : ℝ), g x ∂volume) = ∫ r in Set.Ioi (0 : ℝ), g (-r) ∂volume := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  rw [← MeasureTheory.integral_neg_eq_self]
  congr 1
  ext r
  by_cases hr : 0 < r
  · have h1 : -r ∈ Set.Iio (0 : ℝ) := by simp [hr]
    have h2 : r ∈ Set.Ioi (0 : ℝ) := hr
    simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : -r ∉ Set.Iio (0 : ℝ) := by simp [hr]
    have h2 : r ∉ Set.Ioi (0 : ℝ) := hr
    simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
    let alpha : ℝ := 1;
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) +
      (volume.restrict (Set.Iio (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)));
    T.gaussianVariance = 0 →
    T.levyMeasure = Pi →
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
        -levyTripleExponent T xi =
          ((c * |xi| : ℝ) : ℂ) *
            (1 + Complex.I *
              (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
  intro alpha Pi hVar hPi
  let F : ℝ → ℂ := fun z : ℝ =>
    ∫ r in Set.Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
          Complex.I * (((z * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume
  obtain ⟨k, hk⟩ := Kyprianou.Ch01.stableAlphaOneLogPhaseAllReal
  let c : ℝ := Real.pi * (cpos + cneg) / 2
  let beta : ℝ := (cpos - cneg) / (cpos + cneg)
  let eta : ℝ := -T.drift - (cpos - cneg) * k
  refine ⟨c, beta, eta, ?_, rfl, ?_⟩
  · dsimp [c]; positivity
  intro xi sgn
  let muPos : Measure ℝ :=
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1)))
  let muNeg : Measure ℝ :=
    (volume.restrict (Set.Iio (0 : ℝ))).withDensity
      (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)))
  have hMeasEq : T.levyMeasure = muPos + muNeg := hPi
  have hInt : Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) (muPos + muNeg) := by
    rw [← hMeasEq]
    exact ProbabilityTheory.integrable_levyCompensatedIntegrand T.levyMeasure_isLevyMeasure xi
  have hIntPos : Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muPos :=
    hInt.left_of_add_measure
  have hIntNeg : Integrable (ProbabilityTheory.levyCompensatedIntegrand xi) muNeg :=
    hInt.right_of_add_measure
  have hSplit : -levyTripleExponent T xi =
      -(Complex.I * ((T.drift * xi : ℝ) : ℂ)) +
      (-(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos)) +
      (-(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg)) := by
    unfold levyTripleExponent
    rw [hVar, hMeasEq, integral_add_measure hIntPos hIntNeg]
    simp only [NNReal.coe_zero, zero_mul, zero_div, Complex.ofReal_zero, sub_zero]
    ring
  have hPosEval : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) = (cpos : ℂ) * F xi := by
    dsimp only [muPos]
    have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
    have hflt : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ENNReal.ofReal (cpos * x ^ (-alpha - 1)) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [integral_withDensity_eq_integral_toReal_smul hfm hflt, ← integral_neg]
    have hEq : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        -((ENNReal.ofReal (cpos * r ^ (-alpha - 1))).toReal •
            ProbabilityTheory.levyCompensatedIntegrand xi r) =
        (cpos : ℂ) * (((1 : ℂ) - Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) +
            Complex.I * (((xi * r : ℝ) : ℂ)) * (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr_pos : 0 < r := hr
      have hpow : r ^ (-alpha - 1) = (r ^ (2 : ℕ))⁻¹ := by
        have h1 : (-alpha - 1 : ℝ) = -((2 : ℕ) : ℝ) := by dsimp [alpha]; norm_num
        rw [h1, Real.rpow_neg hr_pos.le, Real.rpow_natCast]
      have hnn : 0 ≤ cpos * r ^ (-alpha - 1) := mul_nonneg hcpos (Real.rpow_nonneg hr_pos.le _)
      rw [ENNReal.toReal_ofReal hnn, hpow, Complex.real_smul,
        ProbabilityTheory.levyCompensatedIntegrand, abs_of_pos hr_pos]
      have hmul_comm : ((r : ℂ) * (xi : ℂ) * Complex.I) = Complex.I * (((xi * r : ℝ) : ℂ)) := by
        push_cast; ring
      rw [hmul_comm]
      push_cast
      ring
    rw [integral_congr_ae hEq, integral_const_mul]
  have hNegEval : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg) = (cneg : ℂ) * F (-xi) := by
    dsimp only [muNeg]
    have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_abs.pow_const _))
    have hflt : ∀ᵐ x ∂(volume.restrict (Set.Iio (0 : ℝ))),
        ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)) < ⊤ :=
      Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    rw [integral_withDensity_eq_integral_toReal_smul hfm hflt, ← integral_neg,
      integral_Iio_zero_eq_Ioi_zero_neg]
    have hEq : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        -((ENNReal.ofReal (cneg * |-r| ^ (-alpha - 1))).toReal •
            ProbabilityTheory.levyCompensatedIntegrand xi (-r)) =
        (cneg : ℂ) * (((1 : ℂ) - Complex.exp (Complex.I * ((((-xi) * r : ℝ) : ℂ))) +
            Complex.I * ((((-xi) * r : ℝ) : ℂ)) * (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr_pos : 0 < r := hr
      rw [abs_neg, abs_of_pos hr_pos]
      have hpow : r ^ (-alpha - 1) = (r ^ (2 : ℕ))⁻¹ := by
        have h1 : (-alpha - 1 : ℝ) = -((2 : ℕ) : ℝ) := by dsimp [alpha]; norm_num
        rw [h1, Real.rpow_neg hr_pos.le, Real.rpow_natCast]
      have hnn : 0 ≤ cneg * r ^ (-alpha - 1) := mul_nonneg hcneg (Real.rpow_nonneg hr_pos.le _)
      rw [ENNReal.toReal_ofReal hnn, hpow, Complex.real_smul,
        ProbabilityTheory.levyCompensatedIntegrand, abs_neg, abs_of_pos hr_pos]
      have hmul_comm : (((-r : ℝ) : ℂ) * (xi : ℂ) * Complex.I) =
          Complex.I * ((((-xi) * r : ℝ) : ℂ)) := by
        push_cast; ring
      rw [hmul_comm]
      push_cast
      ring
    rw [integral_congr_ae hEq, integral_const_mul]
  have hFxi : F xi = (((Real.pi * |xi| / 2 : ℝ) : ℂ) +
      Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
      Complex.I * (((k * xi : ℝ) : ℂ))) := by
    simpa only [F] using hk xi
  have hFnxi : F (-xi) = (((Real.pi * |xi| / 2 : ℝ) : ℂ) -
      Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) +
      Complex.I * (((k * xi : ℝ) : ℂ))) := by
    have h := hk (-xi)
    change F (-xi) = _ at h
    rw [h, abs_neg]
    push_cast
    ring
  have hsign : c * |xi| * beta * (2 / Real.pi) * sgn = (cpos - cneg) * xi := by
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hsum_ne : cpos + cneg ≠ 0 := hnonzero.ne'
    have hxsgn : |xi| * sgn = xi := by
      dsimp [sgn]
      by_cases h1 : 0 < xi
      · rw [if_pos h1, abs_of_pos h1, mul_one]
      · by_cases h2 : xi < 0
        · rw [if_neg h1, if_pos h2, abs_of_neg h2]; ring
        · have h0 : xi = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
          subst h0; simp
    calc c * |xi| * beta * (2 / Real.pi) * sgn
        = (Real.pi * (cpos + cneg) / 2) * ((cpos - cneg) / (cpos + cneg)) * (2 / Real.pi) * (|xi| * sgn) := by
          dsimp [c, beta]; ring
      _ = (cpos - cneg) * xi := by
          rw [hxsgn]; field_simp [hpi_ne, hsum_ne]
  rw [hSplit, hPosEval, hNegEval, hFxi, hFnxi]
  have hlog : (c * |xi| * (beta * (2 / Real.pi) * sgn * Real.log |xi|)) =
      (cpos - cneg) * xi * Real.log |xi| := by
    have : c * |xi| * (beta * (2 / Real.pi) * sgn * Real.log |xi|) =
        (c * |xi| * beta * (2 / Real.pi) * sgn) * Real.log |xi| := by ring
    rw [this, hsign]
  have hc_eq : c * |xi| = Real.pi * (cpos + cneg) * |xi| / 2 := by dsimp [c]; ring
  have heta_eq : eta * xi = -(T.drift * xi) - (cpos - cneg) * k * xi := by dsimp [eta]; ring
  calc -(Complex.I * ((T.drift * xi : ℝ) : ℂ)) +
        (cpos : ℂ) * (((Real.pi * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
          Complex.I * (((k * xi : ℝ) : ℂ))) +
        (cneg : ℂ) * (((Real.pi * |xi| / 2 : ℝ) : ℂ) -
          Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) +
          Complex.I * (((k * xi : ℝ) : ℂ)))
      = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) +
          Complex.I * (((-(T.drift * xi) - (cpos - cneg) * k * xi : ℝ) : ℂ))) := by
        push_cast; ring
    _ = ((c * |xi| : ℝ) : ℂ) *
          (1 + Complex.I *
            (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
        Complex.I * (((eta * xi : ℝ) : ℂ)) := by
        rw [← hc_eq, ← hlog, ← heta_eq]
        push_cast; ring
