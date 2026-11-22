-- Prove2me | solution 1 for Kyprianou.Ch01.stableLevyExponentFormAwayFromOneTargetedV2
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T17:03:46.174805+00:00
-- url     : https://prove2.me/submissions/9d5e8d31-bf85-4787-b21c-0ded8bc76e85

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneFourierGammaAll
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelValue
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneCompensationPowerIntegrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

private lemma integral_Iio_zero_eq_Ioi_zero_neg' {g : ℝ → ℂ} :
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

private lemma exp_alpha_log_neg_I_mul_pos {alpha z : ℝ} (hz : 0 < z) :
    Complex.exp ((alpha : ℂ) * Complex.log (-(Complex.I * (z : ℂ)))) =
      ((z ^ alpha : ℝ) : ℂ) *
        (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
          Complex.I * ((Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) := by
  have hnorm : ‖-(Complex.I * (z : ℂ))‖ = z := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hz]
  have harg : (-(Complex.I * (z : ℂ))).arg = -(Real.pi / 2) := by
    have hEq : -(Complex.I * (z : ℂ)) = (z : ℂ) * (-Complex.I) := by ring
    rw [hEq, Complex.arg_real_mul (-Complex.I) hz, Complex.arg_neg_I]
  have hlog : Complex.log (-(Complex.I * (z : ℂ))) =
      ((Real.log z : ℝ) : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ) := by
    rw [Complex.log, hnorm, harg]
    push_cast; ring
  rw [hlog]
  have hexp_split :
      (alpha : ℂ) * (((Real.log z : ℝ) : ℂ) - Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
        ((alpha * Real.log z : ℝ) : ℂ) + (-(Real.pi * alpha / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp_split, Complex.exp_add, ← Complex.ofReal_exp]
  have hrpow : Real.exp (alpha * Real.log z) = z ^ alpha := by
    rw [Real.rpow_def_of_pos hz, mul_comm]
  rw [hrpow, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

private lemma stable_neg_gamma_cos_pos {alpha : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : alpha ≠ 1) :
    0 < (-Real.Gamma (-alpha)) * Real.cos (Real.pi * alpha / 2) := by
  rcases lt_or_gt_of_ne ha1 with hlt1 | hgt1
  · have hG1 : 0 < Real.Gamma (1 - alpha) := Real.Gamma_pos_of_pos (by linarith)
    have hrec : Real.Gamma (1 - alpha) = (-alpha) * Real.Gamma (-alpha) := by
      have h1 : 1 - alpha = -alpha + 1 := by ring
      rw [h1, Real.Gamma_add_one (by linarith)]
    have hGn : Real.Gamma (-alpha) < 0 := by nlinarith
    have hcos : 0 < Real.cos (Real.pi * alpha / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos]
    nlinarith
  · have hG2 : 0 < Real.Gamma (2 - alpha) := Real.Gamma_pos_of_pos (by linarith)
    have hrec1 : Real.Gamma (2 - alpha) = (1 - alpha) * Real.Gamma (1 - alpha) := by
      have h1 : 2 - alpha = (1 - alpha) + 1 := by ring
      rw [h1, Real.Gamma_add_one (by linarith)]
    have hrec2 : Real.Gamma (1 - alpha) = (-alpha) * Real.Gamma (-alpha) := by
      have h1 : 1 - alpha = -alpha + 1 := by ring
      rw [h1, Real.Gamma_add_one (by linarith)]
    have hGn : 0 < Real.Gamma (-alpha) := by
      have hprod : 0 < (1 - alpha) * (-alpha) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
    have hcos : Real.cos (Real.pi * alpha / 2) < 0 := by
      have h1 : Real.cos (Real.pi * alpha / 2) = -Real.cos (Real.pi - Real.pi * alpha / 2) := by
        rw [Real.cos_pi_sub, neg_neg]
      rw [h1]
      have hpos : 0 < Real.cos (Real.pi - Real.pi * alpha / 2) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> nlinarith [Real.pi_pos]
      linarith
    nlinarith

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ha1 : alpha ≠ 1)
    (hcpos : 0 ≤ cpos) (hcneg : 0 ≤ cneg)
    (hnonzero : 0 < cpos + cneg) :
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
          ((c * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((beta * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
  intro Pi hVar hPi
  -- Common constants
  let K : ℝ := (-Real.Gamma (-alpha)) * Real.cos (Real.pi * alpha / 2)
  have hK_pos : 0 < K := stable_neg_gamma_cos_pos ha0 ha2 ha1
  have hcos_ne : Real.cos (Real.pi * alpha / 2) ≠ 0 := by
    intro h0
    have : K = 0 := by simp [K, h0]
    linarith
  let c : ℝ := K * (cpos + cneg)
  let beta : ℝ := (cpos - cneg) / (cpos + cneg)
  have hc_pos : 0 < c := mul_pos hK_pos hnonzero
  -- The radial one-sided compensated integral J z
  let J : ℝ → ℂ := fun z =>
    ∫ r in Set.Ioi (0 : ℝ),
      ProbabilityTheory.levyCompensatedIntegrand z r * ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume
  -- Evaluation of -J z for all z (whenever the integrand is integrable, or unconditionally for J)
  have hJ_formula : ∃ M : ℝ, ∀ z : ℝ,
      IntegrableOn (fun r : ℝ =>
        ProbabilityTheory.levyCompensatedIntegrand z r * ((r ^ (-alpha - 1) : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) →
      -J z =
        if z = 0 then 0 else
          (((-Real.Gamma (-alpha)) * |z| ^ alpha : ℝ) : ℂ) *
            (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
              Complex.I * (((if 0 < z then (1 : ℝ) else -1) *
                Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) +
          Complex.I * (((M * z : ℝ) : ℂ)) := by
    -- Helper: conjugation symmetry J (-z) = star (J z)
    have hJ_conj : ∀ z : ℝ, J (-z) = star (J z) := fun z => by
      dsimp only [J]
      rw [RCLike.star_def, ← integral_conj]
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      by_cases h1 : |r| < 1 <;>
        simp [ProbabilityTheory.levyCompensatedIntegrand, h1, ← Complex.exp_conj] <;>
        ring_nf
    rcases lt_or_gt_of_ne ha1 with hlt1 | hgt1
    · -- Case 0 < alpha < 1
      let M : ℝ := ∫ r in Set.Ioo (0 : ℝ) 1, r ^ (-alpha) ∂volume
      refine ⟨M, fun z hIntz => ?_⟩
      by_cases hz0 : z = 0
      · subst hz0
        rw [if_pos rfl]
        have h0 : J 0 = 0 := by
          dsimp only [J]
          have hzero : ∀ r : ℝ,
              ProbabilityTheory.levyCompensatedIntegrand 0 r * ((r ^ (-alpha - 1) : ℝ) : ℂ) = 0 := by
            intro r; simp [ProbabilityTheory.levyCompensatedIntegrand]
          simp [hzero]
        rw [h0, neg_zero]
      · rw [if_neg hz0]
        -- Helper for positive z
        have hpos_eval : ∀ w : ℝ, 0 < w →
            IntegrableOn (fun r : ℝ =>
              ProbabilityTheory.levyCompensatedIntegrand w r * ((r ^ (-alpha - 1) : ℝ) : ℂ))
              (Set.Ioi (0 : ℝ)) →
            -J w =
              (((-Real.Gamma (-alpha)) * w ^ alpha : ℝ) : ℂ) *
                (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
                  Complex.I * ((Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) +
              Complex.I * (((M * w : ℝ) : ℂ)) := by
          intro w hw hIntw
          let g1 : ℝ → ℂ := fun r =>
            (Complex.exp ((Complex.I * (w : ℂ)) * (r : ℂ)) - 1) * ((r ^ (-alpha - 1) : ℝ) : ℂ)
          let g2 : ℝ → ℂ := fun r =>
            (Set.Ioo (0 : ℝ) 1).indicator (fun r => Complex.I * (w : ℂ) * ((r ^ (-alpha) : ℝ) : ℂ)) r
          have hg2_int : IntegrableOn g2 (Set.Ioi (0 : ℝ)) := by
            have hbase : IntegrableOn (fun r : ℝ => r ^ (-alpha)) (Set.Ioo (0 : ℝ) 1) :=
              Kyprianou.Ch01.stableAlphaBelowOneCompensationPowerIntegrable alpha ha0 hlt1
            have hbaseC : IntegrableOn (fun r : ℝ => Complex.I * (w : ℂ) * ((r ^ (-alpha) : ℝ) : ℂ))
                (Set.Ioo (0 : ℝ) 1) :=
              (hbase.ofReal).const_mul (Complex.I * (w : ℂ))
            have hind : Integrable g2 volume :=
              (integrable_indicator_iff measurableSet_Ioo).mpr hbaseC
            exact hind.integrableOn
          have hEq_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
              ProbabilityTheory.levyCompensatedIntegrand w r * ((r ^ (-alpha - 1) : ℝ) : ℂ) =
                g1 r - g2 r := by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
            have hr_pos : 0 < r := hr
            dsimp only [g1, g2, ProbabilityTheory.levyCompensatedIntegrand]
            rw [abs_of_pos hr_pos]
            by_cases hr1 : r < 1
            · have hmem : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr_pos, hr1⟩
              rw [if_pos hr1, Set.indicator_of_mem hmem]
              have hpow : r * r ^ (-alpha - 1) = r ^ (-alpha) := by
                have : r ^ (1 : ℝ) * r ^ (-alpha - 1) = r ^ (1 + (-alpha - 1)) :=
                  (Real.rpow_add hr_pos 1 (-alpha - 1)).symm
                simpa using this
              have hpowC : (r : ℂ) * ((r ^ (-alpha - 1) : ℝ) : ℂ) = ((r ^ (-alpha) : ℝ) : ℂ) := by
                exact_mod_cast hpow
              calc (Complex.exp (↑r * ↑w * Complex.I) - 1 - ↑r * ↑w * Complex.I * 1) * ↑(r ^ (-alpha - 1))
                  = (Complex.exp ((Complex.I * ↑w) * ↑r) - 1) * ↑(r ^ (-alpha - 1)) -
                      Complex.I * ↑w * ((r : ℂ) * ↑(r ^ (-alpha - 1))) := by
                    have harg : (r : ℂ) * ↑w * Complex.I = Complex.I * ↑w * ↑r := by ring
                    rw [harg]; ring
                _ = (Complex.exp ((Complex.I * ↑w) * ↑r) - 1) * ↑(r ^ (-alpha - 1)) -
                      Complex.I * ↑w * ↑(r ^ (-alpha)) := by rw [hpowC]
            · have hnot : r ∉ Set.Ioo (0 : ℝ) 1 := fun h => hr1 h.2
              rw [if_neg hr1, Set.indicator_of_notMem hnot]
              have harg : (r : ℂ) * ↑w * Complex.I = Complex.I * ↑w * ↑r := by ring
              rw [harg]; ring
          have hg1_int : IntegrableOn g1 (Set.Ioi (0 : ℝ)) := by
            have hsub : IntegrableOn (fun r => g1 r - g2 r) (Set.Ioi (0 : ℝ)) :=
              hIntw.congr_fun_ae hEq_ae
            exact (hsub.add hg2_int).congr (Filter.Eventually.of_forall fun r => by simp)
          have hJ_split : J w = (∫ r in Set.Ioi (0 : ℝ), g1 r ∂volume) -
              (∫ r in Set.Ioi (0 : ℝ), g2 r ∂volume) := by
            dsimp only [J]
            rw [integral_congr_ae hEq_ae, integral_sub hg1_int hg2_int]
          have hg1_val : (∫ r in Set.Ioi (0 : ℝ), g1 r ∂volume) =
              ((Real.Gamma (-alpha) : ℝ) : ℂ) *
                (((w ^ alpha : ℝ) : ℂ) *
                  (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
                    Complex.I * ((Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ))) := by
            dsimp only [g1]
            rw [Kyprianou.Ch01.stableAlphaBelowOneFourierGammaAll alpha w ha0 hlt1,
              if_neg hw.ne', exp_alpha_log_neg_I_mul_pos hw]
          have hg2_val : (∫ r in Set.Ioi (0 : ℝ), g2 r ∂volume) =
              Complex.I * (((M * w : ℝ) : ℂ)) := by
            dsimp only [g2, M]
            rw [setIntegral_indicator measurableSet_Ioo,
              Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self,
              integral_const_mul]
            have hof : (∫ r in Set.Ioo (0 : ℝ) 1, ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
                ((∫ r in Set.Ioo (0 : ℝ) 1, r ^ (-alpha) ∂volume : ℝ) : ℂ) :=
              integral_ofReal
            rw [hof]
            push_cast; ring
          rw [hJ_split, hg1_val, hg2_val]
          push_cast; ring
        rcases lt_or_gt_of_ne hz0 with hz_neg | hz_pos
        · have hw : 0 < -z := neg_pos.mpr hz_neg
          have hInt_neg : IntegrableOn (fun r : ℝ =>
              ProbabilityTheory.levyCompensatedIntegrand (-z) r * ((r ^ (-alpha - 1) : ℝ) : ℂ))
              (Set.Ioi (0 : ℝ)) := by
            have hconj := Complex.conjCLE.toContinuousLinearMap.integrable_comp hIntz
            refine hconj.congr (Filter.Eventually.of_forall fun r => ?_)
            by_cases h1 : |r| < 1 <;>
              simp [ProbabilityTheory.levyCompensatedIntegrand, h1, ← Complex.exp_conj] <;>
              ring_nf
          have hpos := hpos_eval (-z) hw hInt_neg
          have hJz : -J z = star (-J (-z)) := by
            have h2 : star (J (-z)) = J z := by rw [hJ_conj z, star_star]
            rw [star_neg, h2]
          rw [hJz, hpos, if_neg (not_lt.mpr hz_neg.le), abs_of_neg hz_neg]
          simp only [RCLike.star_def, map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        · rw [if_pos hz_pos, abs_of_pos hz_pos, one_mul]
          exact hpos_eval z hz_pos hIntz
    · -- Case 1 < alpha < 2
      let M : ℝ := -(∫ r in Set.Ioi (1 : ℝ), r ^ (-alpha) ∂volume)
      refine ⟨M, fun z hIntz => ?_⟩
      by_cases hz0 : z = 0
      · subst hz0
        rw [if_pos rfl]
        have h0 : J 0 = 0 := by
          dsimp only [J]
          have hzero : ∀ r : ℝ,
              ProbabilityTheory.levyCompensatedIntegrand 0 r * ((r ^ (-alpha - 1) : ℝ) : ℂ) = 0 := by
            intro r; simp [ProbabilityTheory.levyCompensatedIntegrand]
          simp [hzero]
        rw [h0, neg_zero]
      · rw [if_neg hz0]
        have hpos_eval : ∀ w : ℝ, 0 < w →
            IntegrableOn (fun r : ℝ =>
              ProbabilityTheory.levyCompensatedIntegrand w r * ((r ^ (-alpha - 1) : ℝ) : ℂ))
              (Set.Ioi (0 : ℝ)) →
            -J w =
              (((-Real.Gamma (-alpha)) * w ^ alpha : ℝ) : ℂ) *
                (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
                  Complex.I * ((Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) +
              Complex.I * (((M * w : ℝ) : ℂ)) := by
          intro w hw hIntw
          let g1 : ℝ → ℂ := fun r =>
            (Complex.exp (Complex.I * ((w * r : ℝ) : ℂ)) - 1 -
              Complex.I * ((w * r : ℝ) : ℂ)) / ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
          let g2 : ℝ → ℂ := fun r =>
            (Set.Ioi (1 : ℝ)).indicator (fun r => Complex.I * (w : ℂ) * ((r ^ (-alpha) : ℝ) : ℂ)) r
          have hg2_int : IntegrableOn g2 (Set.Ioi (0 : ℝ)) := by
            have hbase : IntegrableOn (fun r : ℝ => r ^ (-alpha)) (Set.Ioi (1 : ℝ)) :=
              integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
            have hbaseC : IntegrableOn (fun r : ℝ => Complex.I * (w : ℂ) * ((r ^ (-alpha) : ℝ) : ℂ))
                (Set.Ioi (1 : ℝ)) :=
              (hbase.ofReal).const_mul (Complex.I * (w : ℂ))
            exact ((integrable_indicator_iff measurableSet_Ioi).mpr hbaseC).integrableOn
          have hEq_ae : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
              ProbabilityTheory.levyCompensatedIntegrand w r * ((r ^ (-alpha - 1) : ℝ) : ℂ) =
                g1 r + g2 r := by
            have hne1 : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), r ≠ (1 : ℝ) :=
              ae_restrict_of_ae (ae_iff.mpr (by simp [measure_singleton]))
            filter_upwards [ae_restrict_mem measurableSet_Ioi, hne1] with r hr hr1_ne
            have hr_pos : 0 < r := hr
            dsimp only [g1, g2, ProbabilityTheory.levyCompensatedIntegrand]
            rw [abs_of_pos hr_pos]
            have hpow_inv : r ^ (-alpha - 1) = (r ^ (alpha + 1))⁻¹ := by
              have : -alpha - 1 = -(alpha + 1) := by ring
              rw [this, Real.rpow_neg hr_pos.le]
            have hpow_mul : r * r ^ (-alpha - 1) = r ^ (-alpha) := by
              have : r ^ (1 : ℝ) * r ^ (-alpha - 1) = r ^ (1 + (-alpha - 1)) :=
                (Real.rpow_add hr_pos 1 (-alpha - 1)).symm
              simpa using this
            have hpow_mulC : (r : ℂ) * ((r ^ (-alpha - 1) : ℝ) : ℂ) = ((r ^ (-alpha) : ℝ) : ℂ) := by
              exact_mod_cast hpow_mul
            have harg : (r : ℂ) * ↑w * Complex.I = Complex.I * ((w * r : ℝ) : ℂ) := by
              push_cast; ring
            by_cases hr1 : r < 1
            · have hnot : r ∉ Set.Ioi (1 : ℝ) := not_lt.mpr hr1.le
              rw [if_pos hr1, Set.indicator_of_notMem hnot, add_zero, hpow_inv, harg]
              push_cast; ring
            · have hgt1r : r ∈ Set.Ioi (1 : ℝ) := lt_of_le_of_ne (not_lt.mp hr1) (Ne.symm hr1_ne)
              rw [if_neg hr1, Set.indicator_of_mem hgt1r]
              have hinvC : ((r ^ (-alpha - 1) : ℝ) : ℂ) = (((r ^ (alpha + 1) : ℝ) : ℂ))⁻¹ := by
                rw [hpow_inv]; push_cast; rfl
              calc (Complex.exp (↑r * ↑w * Complex.I) - 1 - ↑r * ↑w * Complex.I * 0) * ↑(r ^ (-alpha - 1))
                  = (Complex.exp (Complex.I * ↑(w * r)) - 1 - Complex.I * ↑(w * r)) * ↑(r ^ (-alpha - 1)) +
                      Complex.I * ↑w * ((r : ℂ) * ↑(r ^ (-alpha - 1))) := by
                    rw [harg]; push_cast; ring
                _ = (Complex.exp (Complex.I * ↑(w * r)) - 1 - Complex.I * ↑(w * r)) / ↑(r ^ (alpha + 1)) +
                      Complex.I * ↑w * ↑(r ^ (-alpha)) := by
                    rw [hpow_mulC, hinvC, div_eq_mul_inv]
          have hg1_int : IntegrableOn g1 (Set.Ioi (0 : ℝ)) := by
            have hadd : IntegrableOn (fun r => g1 r + g2 r) (Set.Ioi (0 : ℝ)) :=
              hIntw.congr_fun_ae hEq_ae
            exact (hadd.sub hg2_int).congr (Filter.Eventually.of_forall fun r => by simp)
          have hJ_split : J w = (∫ r in Set.Ioi (0 : ℝ), g1 r ∂volume) +
              (∫ r in Set.Ioi (0 : ℝ), g2 r ∂volume) := by
            dsimp only [J]
            rw [integral_congr_ae hEq_ae, integral_add hg1_int hg2_int]
          have hg1_val : (∫ r in Set.Ioi (0 : ℝ), g1 r ∂volume) =
              ((w ^ alpha : ℝ) : ℂ) *
                (((Real.Gamma (-alpha) : ℝ) : ℂ) *
                  Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))) := by
            -- Change variable u = w * r via integral_comp_mul_left_Ioi
            let h0 : ℝ → ℂ := fun u =>
              (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ)) /
                ((((u : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
            have hscale : ∀ r ∈ Set.Ioi (0 : ℝ),
                g1 r = ((w ^ (alpha + 1) : ℝ) : ℂ) * h0 (w * r) := by
              intro r hr
              have hr_pos : 0 < r := hr
              dsimp only [g1, h0]
              have hmul : (w * r) ^ (alpha + 1) = w ^ (alpha + 1) * r ^ (alpha + 1) :=
                Real.mul_rpow hw.le hr_pos.le
              have hw_ne : ((w ^ (alpha + 1) : ℝ) : ℂ) ≠ 0 := by
                exact_mod_cast (Real.rpow_pos_of_pos hw (alpha + 1)).ne'
              rw [hmul]
              push_cast
              field_simp [hw_ne]
            rw [setIntegral_congr_fun measurableSet_Ioi hscale, integral_const_mul]
            have hcomp := MeasureTheory.integral_comp_mul_left_Ioi h0 (0 : ℝ) hw
            simp only [mul_zero] at hcomp
            rw [hcomp, Kyprianou.Ch01.stableAlphaAboveOneKernelValue alpha hgt1 ha2]
            have hpow : w ^ (alpha + 1) * w⁻¹ = w ^ alpha := by
              rw [Real.rpow_add hw, Real.rpow_one, mul_assoc, mul_inv_cancel₀ hw.ne', mul_one]
            rw [Complex.real_smul]
            have hpowC : ((w ^ (alpha + 1) : ℝ) : ℂ) * ((w⁻¹ : ℝ) : ℂ) = ((w ^ alpha : ℝ) : ℂ) := by
              exact_mod_cast hpow
            calc ((w ^ (alpha + 1) : ℝ) : ℂ) * (((w⁻¹ : ℝ) : ℂ) *
                    (((Real.Gamma (-alpha) : ℝ) : ℂ) *
                      Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))))
                = (((w ^ (alpha + 1) : ℝ) : ℂ) * ((w⁻¹ : ℝ) : ℂ)) *
                    (((Real.Gamma (-alpha) : ℝ) : ℂ) *
                      Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))) := by ring
              _ = ((w ^ alpha : ℝ) : ℂ) *
                    (((Real.Gamma (-alpha) : ℝ) : ℂ) *
                      Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ)))) := by rw [hpowC]
          have hg2_val : (∫ r in Set.Ioi (0 : ℝ), g2 r ∂volume) =
              -(Complex.I * (((M * w : ℝ) : ℂ))) := by
            dsimp only [g2, M]
            rw [setIntegral_indicator measurableSet_Ioi,
              Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one),
              integral_const_mul]
            have hof : (∫ r in Set.Ioi (1 : ℝ), ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
                ((∫ r in Set.Ioi (1 : ℝ), r ^ (-alpha) ∂volume : ℝ) : ℂ) :=
              integral_ofReal
            rw [hof]
            push_cast; ring
          have hexp_euler : Complex.exp (-(Complex.I * ((Real.pi * alpha / 2) : ℂ))) =
              ((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
                Complex.I * ((Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ) := by
            have h1 : -(Complex.I * ((Real.pi * alpha / 2) : ℂ)) =
                ((-(Real.pi * alpha / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
            rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
              Real.cos_neg, Real.sin_neg]
            push_cast; ring
          rw [hJ_split, hg1_val, hg2_val, hexp_euler]
          push_cast; ring
        rcases lt_or_gt_of_ne hz0 with hz_neg | hz_pos
        · have hw : 0 < -z := neg_pos.mpr hz_neg
          have hInt_neg : IntegrableOn (fun r : ℝ =>
              ProbabilityTheory.levyCompensatedIntegrand (-z) r * ((r ^ (-alpha - 1) : ℝ) : ℂ))
              (Set.Ioi (0 : ℝ)) := by
            have hconj := Complex.conjCLE.toContinuousLinearMap.integrable_comp hIntz
            refine hconj.congr (Filter.Eventually.of_forall fun r => ?_)
            by_cases h1 : |r| < 1 <;>
              simp [ProbabilityTheory.levyCompensatedIntegrand, h1, ← Complex.exp_conj] <;>
              ring_nf
          have hpos := hpos_eval (-z) hw hInt_neg
          have hJz : -J z = star (-J (-z)) := by
            have h2 : star (J (-z)) = J z := by rw [hJ_conj z, star_star]
            rw [star_neg, h2]
          rw [hJz, hpos, if_neg (not_lt.mpr hz_neg.le), abs_of_neg hz_neg]
          simp only [RCLike.star_def, map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
          push_cast; ring
        · rw [if_pos hz_pos, abs_of_pos hz_pos, one_mul]
          exact hpos_eval z hz_pos hIntz
  obtain ⟨M, hM⟩ := hJ_formula
  let eta : ℝ := -T.drift + (cpos - cneg) * M
  refine ⟨c, beta, eta, hc_pos, rfl, ?_⟩
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
  -- Evaluate positive and negative measure contributions
  have hPosPart : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muPos) =
      if xi = 0 then 0 else
        (cpos : ℂ) * ((((-Real.Gamma (-alpha)) * |xi| ^ alpha : ℝ) : ℂ) *
          (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
            Complex.I * (((if 0 < xi then (1 : ℝ) else -1) *
              Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) +
          Complex.I * (((M * xi : ℝ) : ℂ))) := by
    rcases eq_or_lt_of_le hcpos with rfl | hcpos_pos
    · have hmu0 : muPos = 0 := by
        dsimp only [muPos]
        simp
      rw [hmu0, integral_zero_measure, neg_zero]
      split_ifs <;> simp
    · dsimp only [muPos] at hIntPos ⊢
      have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
      have hflt : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          ENNReal.ofReal (cpos * x ^ (-alpha - 1)) < ⊤ :=
        Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
      have hInt_rad : IntegrableOn (fun r : ℝ =>
          ProbabilityTheory.levyCompensatedIntegrand xi r * ((r ^ (-alpha - 1) : ℝ) : ℂ))
          (Set.Ioi (0 : ℝ)) := by
        have hfm_nn : Measurable (fun x : ℝ => Real.toNNReal (cpos * x ^ (-alpha - 1))) :=
          (measurable_const.mul (measurable_id.pow_const _)).real_toNNReal
        have hIntPos' : Integrable (ProbabilityTheory.levyCompensatedIntegrand xi)
            ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
              (fun x : ℝ => ((Real.toNNReal (cpos * x ^ (-alpha - 1)) : ℝ≥0) : ℝ≥0∞))) := hIntPos
        have h1 := (integrable_withDensity_iff_integrable_smul₀ hfm_nn.aemeasurable).mp hIntPos'
        have h2 := h1.const_mul ((cpos⁻¹ : ℝ) : ℂ)
        refine h2.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr_pos : 0 < r := hr
        have hnn : 0 ≤ cpos * r ^ (-alpha - 1) := mul_nonneg hcpos_pos.le (Real.rpow_nonneg hr_pos.le _)
        change ((cpos⁻¹ : ℝ) : ℂ) * ((Real.toNNReal (cpos * r ^ (-alpha - 1)) : ℝ≥0) •
            ProbabilityTheory.levyCompensatedIntegrand xi r) = _
        rw [NNReal.smul_def, Real.coe_toNNReal _ hnn, Complex.real_smul]
        have hcne : (cpos : ℂ) ≠ 0 := by exact_mod_cast hcpos_pos.ne'
        push_cast; field_simp [hcne]
      have hEval : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂
          ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
            (fun x : ℝ => ENNReal.ofReal (cpos * x ^ (-alpha - 1))))) = (cpos : ℂ) * (-J xi) := by
        rw [integral_withDensity_eq_integral_toReal_smul hfm hflt]
        have hEq : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            (ENNReal.ofReal (cpos * r ^ (-alpha - 1))).toReal •
              ProbabilityTheory.levyCompensatedIntegrand xi r =
            (cpos : ℂ) * (ProbabilityTheory.levyCompensatedIntegrand xi r *
              ((r ^ (-alpha - 1) : ℝ) : ℂ)) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          have hr_pos : 0 < r := hr
          have hnn : 0 ≤ cpos * r ^ (-alpha - 1) := mul_nonneg hcpos_pos.le (Real.rpow_nonneg hr_pos.le _)
          rw [ENNReal.toReal_ofReal hnn, Complex.real_smul]
          push_cast; ring
        rw [integral_congr_ae hEq, integral_const_mul]
        dsimp only [J]; ring
      rw [hEval, hM xi hInt_rad]
      split_ifs <;> simp
  have hNegPart : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂muNeg) =
      if xi = 0 then 0 else
        (cneg : ℂ) * ((((-Real.Gamma (-alpha)) * |xi| ^ alpha : ℝ) : ℂ) *
          (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
            Complex.I * (((if 0 < -xi then (1 : ℝ) else -1) *
              Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) +
          Complex.I * (((M * (-xi) : ℝ) : ℂ))) := by
    rcases eq_or_lt_of_le hcneg with rfl | hcneg_pos
    · have hmu0 : muNeg = 0 := by
        dsimp only [muNeg]
        simp
      rw [hmu0, integral_zero_measure, neg_zero]
      split_ifs <;> simp
    · dsimp only [muNeg] at hIntNeg ⊢
      have hfm : Measurable (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1))) :=
        ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_abs.pow_const _))
      have hflt : ∀ᵐ x ∂(volume.restrict (Set.Iio (0 : ℝ))),
          ENNReal.ofReal (cneg * |x| ^ (-alpha - 1)) < ⊤ :=
        Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
      have hInt_rad : IntegrableOn (fun r : ℝ =>
          ProbabilityTheory.levyCompensatedIntegrand (-xi) r * ((r ^ (-alpha - 1) : ℝ) : ℂ))
          (Set.Ioi (0 : ℝ)) := by
        have hfm_nn : Measurable (fun x : ℝ => Real.toNNReal (cneg * |x| ^ (-alpha - 1))) :=
          (measurable_const.mul (measurable_abs.pow_const _)).real_toNNReal
        have hIntNeg' : Integrable (ProbabilityTheory.levyCompensatedIntegrand xi)
            ((volume.restrict (Set.Iio (0 : ℝ))).withDensity
              (fun x : ℝ => ((Real.toNNReal (cneg * |x| ^ (-alpha - 1)) : ℝ≥0) : ℝ≥0∞))) := hIntNeg
        have h1 := (integrable_withDensity_iff_integrable_smul₀ hfm_nn.aemeasurable).mp hIntNeg'
        have h1_ind : Integrable ((Set.Iio (0 : ℝ)).indicator (fun x =>
            (Real.toNNReal (cneg * |x| ^ (-alpha - 1)) : ℝ≥0) •
              ProbabilityTheory.levyCompensatedIntegrand xi x)) volume :=
          (integrable_indicator_iff measurableSet_Iio).mpr h1
        have h1_neg : Integrable (fun r =>
            (Set.Iio (0 : ℝ)).indicator (fun x =>
              (Real.toNNReal (cneg * |x| ^ (-alpha - 1)) : ℝ≥0) •
                ProbabilityTheory.levyCompensatedIntegrand xi x) (-r)) volume :=
          h1_ind.comp_neg
        have h1_oi : IntegrableOn (fun r =>
            (Real.toNNReal (cneg * |-r| ^ (-alpha - 1)) : ℝ≥0) •
              ProbabilityTheory.levyCompensatedIntegrand xi (-r)) (Set.Ioi (0 : ℝ)) := by
          rw [← integrable_indicator_iff measurableSet_Ioi]
          refine h1_neg.congr (Filter.Eventually.of_forall fun r => ?_)
          by_cases hr : 0 < r
          · have h1m : -r ∈ Set.Iio (0 : ℝ) := by simp [hr]
            have hr' : r ∈ Set.Ioi (0 : ℝ) := hr
            dsimp only
            rw [Set.indicator_of_mem h1m, Set.indicator_of_mem hr']
          · have h1m : -r ∉ Set.Iio (0 : ℝ) := by simp [hr]
            have hr' : r ∉ Set.Ioi (0 : ℝ) := hr
            dsimp only
            rw [Set.indicator_of_notMem h1m, Set.indicator_of_notMem hr']
        have h2 := h1_oi.const_mul ((cneg⁻¹ : ℝ) : ℂ)
        refine h2.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        have hr_pos : 0 < r := hr
        change ((cneg⁻¹ : ℝ) : ℂ) * ((Real.toNNReal (cneg * |-r| ^ (-alpha - 1)) : ℝ≥0) •
            ProbabilityTheory.levyCompensatedIntegrand xi (-r)) = _
        rw [abs_neg, abs_of_pos hr_pos]
        have hnn : 0 ≤ cneg * r ^ (-alpha - 1) := mul_nonneg hcneg_pos.le (Real.rpow_nonneg hr_pos.le _)
        rw [NNReal.smul_def, Real.coe_toNNReal _ hnn, Complex.real_smul]
        have hlc : ProbabilityTheory.levyCompensatedIntegrand xi (-r) =
            ProbabilityTheory.levyCompensatedIntegrand (-xi) r := by
          simp only [ProbabilityTheory.levyCompensatedIntegrand, abs_neg]
          push_cast; ring_nf
        rw [hlc]
        have hcne : (cneg : ℂ) ≠ 0 := by exact_mod_cast hcneg_pos.ne'
        push_cast; field_simp [hcne]
      have hEval : -(∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂
          ((volume.restrict (Set.Iio (0 : ℝ))).withDensity
            (fun x : ℝ => ENNReal.ofReal (cneg * |x| ^ (-alpha - 1))))) = (cneg : ℂ) * (-J (-xi)) := by
        rw [integral_withDensity_eq_integral_toReal_smul hfm hflt,
          integral_Iio_zero_eq_Ioi_zero_neg']
        have hEq : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
            (ENNReal.ofReal (cneg * |-r| ^ (-alpha - 1))).toReal •
              ProbabilityTheory.levyCompensatedIntegrand xi (-r) =
            (cneg : ℂ) * (ProbabilityTheory.levyCompensatedIntegrand (-xi) r *
              ((r ^ (-alpha - 1) : ℝ) : ℂ)) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          have hr_pos : 0 < r := hr
          rw [abs_neg, abs_of_pos hr_pos]
          have hnn : 0 ≤ cneg * r ^ (-alpha - 1) := mul_nonneg hcneg_pos.le (Real.rpow_nonneg hr_pos.le _)
          rw [ENNReal.toReal_ofReal hnn, Complex.real_smul]
          have hlc : ProbabilityTheory.levyCompensatedIntegrand xi (-r) =
              ProbabilityTheory.levyCompensatedIntegrand (-xi) r := by
            simp only [ProbabilityTheory.levyCompensatedIntegrand, abs_neg]
            push_cast; ring_nf
          rw [hlc]
          push_cast; ring
        rw [integral_congr_ae hEq, integral_const_mul]
        dsimp only [J]; ring
      rw [hEval, hM (-xi) hInt_rad, abs_neg]
      by_cases hxi0 : xi = 0
      · subst hxi0; simp
      · have hnxi0 : -xi ≠ 0 := neg_ne_zero.mpr hxi0
        rw [if_neg hnxi0, if_neg hxi0]
  rw [hSplit, hPosPart, hNegPart]
  by_cases hxi0 : xi = 0
  · subst hxi0
    simp [Real.zero_rpow ha0.ne']
  · rw [if_neg hxi0, if_neg hxi0]
    have hsgn_pos : (if 0 < xi then (1 : ℝ) else -1) = sgn := by
      dsimp only [sgn]
      rcases lt_or_gt_of_ne hxi0 with hneg | hpos
      · rw [if_neg (not_lt.mpr hneg.le), if_neg (not_lt.mpr hneg.le), if_pos hneg]
      · rw [if_pos hpos, if_pos hpos]
    have hsgn_neg : (if 0 < -xi then (1 : ℝ) else -1) = -sgn := by
      dsimp only [sgn]
      rcases lt_or_gt_of_ne hxi0 with hneg | hpos
      · rw [if_pos (neg_pos.mpr hneg), if_neg (not_lt.mpr hneg.le), if_pos hneg]; ring
      · rw [if_neg (not_lt.mpr (neg_nonpos.mpr hpos.le)), if_pos hpos]
    rw [hsgn_pos, hsgn_neg]
    have hsum_ne : cpos + cneg ≠ 0 := hnonzero.ne'
    have htan_id : c * (beta * Real.tan (Real.pi * alpha / 2) * sgn) =
        (-Real.Gamma (-alpha)) * Real.sin (Real.pi * alpha / 2) * (cpos - cneg) * sgn := by
      dsimp only [c, K, beta]
      rw [Real.tan_eq_sin_div_cos]
      have h1 : (-Real.Gamma (-alpha)) * Real.cos (Real.pi * alpha / 2) * (cpos + cneg) *
          ((cpos - cneg) / (cpos + cneg) * (Real.sin (Real.pi * alpha / 2) / Real.cos (Real.pi * alpha / 2)) * sgn) =
          (-Real.Gamma (-alpha)) * (Real.cos (Real.pi * alpha / 2) / Real.cos (Real.pi * alpha / 2)) *
          ((cpos + cneg) / (cpos + cneg)) * Real.sin (Real.pi * alpha / 2) * (cpos - cneg) * sgn := by ring
      rw [h1, div_self hcos_ne, div_self hsum_ne, mul_one, mul_one]
    have hc_eq : c = (-Real.Gamma (-alpha)) * Real.cos (Real.pi * alpha / 2) * (cpos + cneg) := rfl
    have heta_eq : eta * xi = -(T.drift * xi) + cpos * (M * xi) + cneg * (M * (-xi)) := by
      dsimp only [eta]; ring
    calc -(Complex.I * ((T.drift * xi : ℝ) : ℂ)) +
          (cpos : ℂ) * ((((-Real.Gamma (-alpha)) * |xi| ^ alpha : ℝ) : ℂ) *
            (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
              Complex.I * ((sgn * Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) +
            Complex.I * (((M * xi : ℝ) : ℂ))) +
          (cneg : ℂ) * ((((-Real.Gamma (-alpha)) * |xi| ^ alpha : ℝ) : ℂ) *
            (((Real.cos (Real.pi * alpha / 2) : ℝ) : ℂ) -
              Complex.I * (((-sgn) * Real.sin (Real.pi * alpha / 2) : ℝ) : ℂ)) +
            Complex.I * (((M * (-xi) : ℝ) : ℂ)))
        = ((((-Real.Gamma (-alpha)) * Real.cos (Real.pi * alpha / 2) * (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) -
            Complex.I * ((((-Real.Gamma (-alpha)) * Real.sin (Real.pi * alpha / 2) * (cpos - cneg) * sgn) *
              |xi| ^ alpha : ℝ) : ℂ) +
            Complex.I * (((-(T.drift * xi) + cpos * (M * xi) + cneg * (M * (-xi)) : ℝ) : ℂ)) := by
          push_cast; ring
      _ = ((c * |xi| ^ alpha : ℝ) : ℂ) *
            (1 - Complex.I *
              (((beta * Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ)) := by
          rw [← hc_eq, ← htan_id, ← heta_eq]
          push_cast; ring
