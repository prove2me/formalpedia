-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFullLevyTripletV2
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T15:24:35.659751+00:00
-- url     : https://prove2.me/submissions/4952f33e-66ad-482c-bf3c-9e82a13cb4de

import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))));
    let drift : ℝ :=
      -(2 * s / b) *
        (∫ y in (0 : ℝ)..b,
          Real.exp (-(y ^ 2 / 2)) / Real.sqrt (2 * Real.pi) ∂volume);
    (s * ∫ x in Set.Ioo (0 : ℝ) (1 : ℝ), x ∂Pi) = -drift ∧
      ∃ T : ProbabilityTheory.LevyKhintchineTriple,
        T.gaussianVariance = 0 ∧
          T.levyMeasure = (ENNReal.ofReal s) • Pi ∧
          T.drift = drift := by
  intro Pi drift
  set f : ℝ → ℝ := fun x =>
    (1 / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-(b ^ 2 * x / 2)) with hf_def
  have hf_meas : Measurable f := by
    have h1 : Measurable (fun x : ℝ => 2 * Real.pi * x ^ 3) :=
      measurable_const.mul (measurable_id.pow_const 3)
    have h2 : Measurable (fun x : ℝ => 1 / Real.sqrt (2 * Real.pi * x ^ 3)) :=
      measurable_const.div (Real.continuous_sqrt.measurable.comp h1)
    have h3 : Measurable (fun x : ℝ => Real.exp (-(b ^ 2 * x / 2))) :=
      Real.continuous_exp.measurable.comp
        (((measurable_const.mul measurable_id).div_const 2).neg)
    exact h2.mul h3
  have hf_nonneg : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    dsimp [f]
    positivity
  have hofReal_meas : Measurable (fun x : ℝ => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf_meas
  constructor
  · -- Part 1: (s * ∫ x in Ioo 0 1, x ∂Pi) = -drift
    have hPi_restrict :
        Pi.restrict (Set.Ioo (0 : ℝ) 1) =
          (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity
            (fun x => ENNReal.ofReal (f x)) := by
      dsimp [Pi]
      rw [restrict_withDensity measurableSet_Ioo,
        Measure.restrict_restrict_of_subset Set.Ioo_subset_Ioi_self]
    have hInt_eq :
        ∫ x in Set.Ioo (0 : ℝ) 1, x ∂Pi =
          ∫ x in Set.Ioo (0 : ℝ) 1, f x * x ∂volume := by
      rw [hPi_restrict, integral_withDensity_eq_integral_toReal_smul hofReal_meas
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hf_nonneg x)]
    -- Change of variables φ(y) = y^2 / b^2 mapping (0, b) onto (0, 1)
    let φ : ℝ → ℝ := fun y => y ^ 2 / b ^ 2
    let φ' : ℝ → ℝ := fun y => 2 * y / b ^ 2
    have hφ_image : φ '' Set.Ioo (0 : ℝ) b = Set.Ioo (0 : ℝ) 1 := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy0, hyb⟩, rfl⟩
        refine ⟨by positivity, ?_⟩
        dsimp [φ]
        rw [div_lt_one (sq_pos_of_pos hb)]
        exact sq_lt_sq' (by linarith) hyb
      · rintro ⟨hx0, hx1⟩
        refine ⟨b * Real.sqrt x, ⟨by positivity, ?_⟩, ?_⟩
        · have hsq : Real.sqrt x < 1 := by
            rw [Real.sqrt_lt' one_pos]
            simpa using hx1
          nlinarith
        · dsimp [φ]
          rw [mul_pow, Real.sq_sqrt hx0.le]
          field_simp [hb.ne']
    have hφ_inj : Set.InjOn φ (Set.Ioo (0 : ℝ) b) := by
      intro y₁ hy₁ y₂ hy₂ hEq
      dsimp [φ] at hEq
      have hsq : y₁ ^ 2 = y₂ ^ 2 := by
        have hb2 : b ^ 2 ≠ 0 := (sq_pos_of_pos hb).ne'
        exact (div_left_inj' hb2).mp hEq
      nlinarith [hy₁.1, hy₂.1]
    have hφ_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) b,
        HasDerivWithinAt φ (φ' y) (Set.Ioo (0 : ℝ) b) y := by
      intro y _
      have hd : HasDerivAt φ (φ' y) y := by
        dsimp [φ, φ']
        have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y ^ (2 - 1)) y :=
          hasDerivAt_pow 2 y
        simpa [pow_one] using h1.div_const (b ^ 2)
      exact hd.hasDerivWithinAt
    have hSub :
        ∫ x in Set.Ioo (0 : ℝ) 1, f x * x ∂volume =
          ∫ y in Set.Ioo (0 : ℝ) b, |φ' y| * (f (φ y) * φ y) ∂volume := by
      rw [← hφ_image]
      simpa [smul_eq_mul] using
        (integral_image_eq_integral_abs_deriv_smul (f := φ) (f' := φ')
          (g := fun x => f x * x) measurableSet_Ioo hφ_deriv hφ_inj)
    have hIntegrand :
        ∀ y ∈ Set.Ioo (0 : ℝ) b,
          |φ' y| * (f (φ y) * φ y) =
            (2 / b) * (Real.exp (-(y ^ 2 / 2)) / Real.sqrt (2 * Real.pi)) := by
      intro y hy
      have hy0 : 0 < y := hy.1
      have hφ'pos : 0 < φ' y := by dsimp [φ']; positivity
      rw [abs_of_pos hφ'pos]
      dsimp [f, φ, φ']
      have hexp : b ^ 2 * (y ^ 2 / b ^ 2) / 2 = y ^ 2 / 2 := by
        field_simp [hb.ne']
      rw [hexp]
      have hsqrt_pow : Real.sqrt (2 * Real.pi * (y ^ 2 / b ^ 2) ^ 3) =
          Real.sqrt (2 * Real.pi) * (y ^ 3 / b ^ 3) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
        congr 1
        have hpow : (y ^ 2 / b ^ 2) ^ 3 = (y ^ 3 / b ^ 3) ^ 2 := by ring
        rw [hpow, Real.sqrt_sq (by positivity)]
      rw [hsqrt_pow]
      have hpi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
      field_simp [hb.ne', hy0.ne', hpi]
    have hEq2 :
        ∫ y in Set.Ioo (0 : ℝ) b, |φ' y| * (f (φ y) * φ y) ∂volume =
          (2 / b) * ∫ y in (0 : ℝ)..b,
            Real.exp (-(y ^ 2 / 2)) / Real.sqrt (2 * Real.pi) ∂volume := by
      rw [setIntegral_congr_fun measurableSet_Ioo hIntegrand,
        integral_const_mul,
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hb.le]
    rw [hInt_eq, hSub, hEq2]
    dsimp [drift]
    ring
  · -- Part 2: construct LevyKhintchineTriple
    have hPi_zero : Pi ({0} : Set ℝ) = 0 := by
      dsimp [Pi]
      rw [withDensity_apply _ (measurableSet_singleton 0)]
      have hdisj : (volume.restrict (Set.Ioi (0 : ℝ))).restrict ({0} : Set ℝ) = 0 := by
        rw [Measure.restrict_restrict (measurableSet_singleton 0)]
        have hemp : ({0} : Set ℝ) ∩ Set.Ioi (0 : ℝ) = ∅ := by
          ext x; simp
        rw [hemp, Measure.restrict_empty]
      rw [hdisj, lintegral_zero_measure]
    have hPi_lintegral :
        ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂Pi < ⊤ := by
      have hmin_meas : Measurable (fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id.pow_const 2))
      dsimp only [Pi]
      change (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂
        ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (f x)))) < ⊤
      rw [lintegral_withDensity_eq_lintegral_mul _ hofReal_meas hmin_meas]
      have hSplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
        ext x
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
        constructor
        · intro hx
          by_cases h1 : x ≤ 1
          · exact Or.inl ⟨hx, h1⟩
          · exact Or.inr (lt_of_not_ge h1)
        · rintro (⟨hx, _⟩ | hx)
          · exact hx
          · linarith
      rw [hSplit]
      calc ∫⁻ x in Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ),
            ENNReal.ofReal (f x) * ENNReal.ofReal (min 1 (x ^ 2)) ∂volume
          ≤ (∫⁻ x in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal (f x) * ENNReal.ofReal (min 1 (x ^ 2)) ∂volume) +
            (∫⁻ x in Set.Ioi (1 : ℝ),
              ENNReal.ofReal (f x) * ENNReal.ofReal (min 1 (x ^ 2)) ∂volume) :=
            lintegral_union_le _ _ _
        _ < ⊤ := by
            refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
            · -- Bound on (0, 1] by constant 1 / sqrt(2π)
              have hC : ∀ x ∈ Set.Ioc (0 : ℝ) 1,
                  ENNReal.ofReal (f x) * ENNReal.ofReal (min 1 (x ^ 2)) ≤
                    ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) := by
                intro x hx
                rw [← ENNReal.ofReal_mul (hf_nonneg x)]
                apply ENNReal.ofReal_le_ofReal
                have hx0 : 0 < x := hx.1
                have hx1 : x ≤ 1 := hx.2
                have hexp : Real.exp (-(b ^ 2 * x / 2)) ≤ 1 :=
                  Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg b])
                have hmin : min 1 (x ^ 2) ≤ x ^ 2 := min_le_right _ _
                have hsqrt_eq : Real.sqrt (2 * Real.pi * x ^ 3) =
                    Real.sqrt (2 * Real.pi) * (x * Real.sqrt x) := by
                  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
                  congr 1
                  have : x ^ 3 = x ^ 2 * x := by ring
                  rw [this, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx0.le]
                have hsqx : Real.sqrt x ≤ 1 := by
                  rw [Real.sqrt_le_one]; exact hx1
                calc f x * min 1 (x ^ 2)
                    ≤ f x * x ^ 2 := mul_le_mul_of_nonneg_left hmin (hf_nonneg x)
                  _ = (1 / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-(b ^ 2 * x / 2)) * x ^ 2 := rfl
                  _ ≤ (1 / Real.sqrt (2 * Real.pi * x ^ 3)) * 1 * x ^ 2 := by
                      gcongr
                  _ = (1 / Real.sqrt (2 * Real.pi)) * Real.sqrt x := by
                      rw [hsqrt_eq]
                      have hpi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
                      have hrx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
                      have hrx2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
                      field_simp [hx0.ne', hpi, hrx]
                      nlinarith [hrx2]
                  _ ≤ (1 / Real.sqrt (2 * Real.pi)) * 1 := by
                      gcongr
                  _ = 1 / Real.sqrt (2 * Real.pi) := mul_one _
              calc ∫⁻ x in Set.Ioc (0 : ℝ) 1,
                    ENNReal.ofReal (f x) * ENNReal.ofReal (min 1 (x ^ 2)) ∂volume
                  ≤ ∫⁻ _ in Set.Ioc (0 : ℝ) 1,
                      ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) ∂volume :=
                    setLIntegral_mono' measurableSet_Ioc hC
                _ = ENNReal.ofReal (1 / Real.sqrt (2 * Real.pi)) * volume (Set.Ioc (0 : ℝ) 1) := by
                    rw [setLIntegral_const]
                _ < ⊤ := by
                    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
                    rw [Real.volume_Ioc]
                    exact ENNReal.ofReal_lt_top
            · -- Bound on (1, ∞) by (1 / sqrt(2π)) * x^(-3/2)
              have hInt_tail : IntegrableOn
                  (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * x ^ (-(3 : ℝ) / 2))
                  (Set.Ioi (1 : ℝ)) volume :=
                (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) zero_lt_one).const_mul _
              have hTail : ∀ x ∈ Set.Ioi (1 : ℝ),
                  ENNReal.ofReal (f x) * ENNReal.ofReal (min 1 (x ^ 2)) ≤
                    ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi)) * x ^ (-(3 : ℝ) / 2)) := by
                intro x hx
                rw [← ENNReal.ofReal_mul (hf_nonneg x)]
                apply ENNReal.ofReal_le_ofReal
                have hx1 : 1 < x := hx
                have hx0 : 0 < x := by linarith
                have hexp : Real.exp (-(b ^ 2 * x / 2)) ≤ 1 :=
                  Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg b])
                have hmin : min 1 (x ^ 2) ≤ 1 := min_le_left _ _
                have hsqrt_rpow : (Real.sqrt (x ^ 3))⁻¹ = x ^ (-(3 : ℝ) / 2) := by
                  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx0.le,
                    ← Real.rpow_neg hx0.le]
                  norm_num
                calc f x * min 1 (x ^ 2)
                    ≤ f x * 1 := mul_le_mul_of_nonneg_left hmin (hf_nonneg x)
                  _ = (1 / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-(b ^ 2 * x / 2)) := by
                      rw [mul_one]
                  _ ≤ (1 / Real.sqrt (2 * Real.pi * x ^ 3)) * 1 := by gcongr
                  _ = (1 / Real.sqrt (2 * Real.pi)) * x ^ (-(3 : ℝ) / 2) := by
                      rw [mul_one, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),
                        one_div, mul_inv, ← one_div, hsqrt_rpow]
              calc ∫⁻ x in Set.Ioi (1 : ℝ),
                    ENNReal.ofReal (f x) * ENNReal.ofReal (min 1 (x ^ 2)) ∂volume
                  ≤ ∫⁻ x in Set.Ioi (1 : ℝ),
                      ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi)) * x ^ (-(3 : ℝ) / 2)) ∂volume :=
                    setLIntegral_mono' measurableSet_Ioi hTail
                _ < ⊤ := hInt_tail.lintegral_lt_top
    have hLevy : ProbabilityTheory.IsLevyMeasure ((ENNReal.ofReal s) • Pi) := by
      refine ⟨?_, ?_⟩
      · simp [hPi_zero]
      · rw [lintegral_smul_measure]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPi_lintegral
    exact ⟨{
      drift := drift
      gaussianVariance := 0
      levyMeasure := (ENNReal.ofReal s) • Pi
      levyMeasure_isLevyMeasure := hLevy
    }, rfl, rfl, rfl⟩
