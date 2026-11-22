-- Prove2me | solution 1 for MasulloRepair.localized_fourier_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T20:11:55.329195+00:00
-- url     : https://prove2.me/submissions/5ec79482-6f70-495c-8ead-179580039bb3

import Theorems.Thm_MasulloRepair_L2_kernel_composition_nuclear
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 800000

open MasulloGRH MasulloRepair MeasureTheory

private theorem l2_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div (2 : ℝ),
    ← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]

private theorem unit_phase_kernel (a r : ℝ → ℂ) (χ : ℝ × ℝ → ℂ)
    (ha : MemLp a 2 volume) (hr : MemLp r 2 volume)
    (hχ : AEStronglyMeasurable χ (volume.prod volume))
    (hχnorm : ∀ p, ‖χ p‖ = 1) :
    MemLp (fun p : ℝ × ℝ => a p.1 * χ p * r p.2) 2 (volume.prod volume) ∧
      (eLpNorm (fun p : ℝ × ℝ => a p.1 * χ p * r p.2) 2
        (volume.prod volume)).toReal =
        (eLpNorm a 2 volume).toReal * (eLpNorm r 2 volume).toReal := by
  have hm := (ha.1.comp_fst.mul hχ).mul hr.1.comp_snd
  have heq (p : ℝ × ℝ) : ‖a p.1 * χ p * r p.2‖ ^ 2 =
      ‖a p.1‖ ^ 2 * ‖r p.2‖ ^ 2 := by
    rw [norm_mul, norm_mul, hχnorm, mul_one, mul_pow]
  have hk : MemLp (fun p : ℝ × ℝ => a p.1 * χ p * r p.2) 2
      (volume.prod volume) := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    change Integrable (fun p : ℝ × ℝ => ‖a p.1 * χ p * r p.2‖ ^ 2)
      (volume.prod volume)
    simp_rw [heq]
    exact ((memLp_two_iff_integrable_sq_norm ha.1).mp ha).mul_prod
      ((memLp_two_iff_integrable_sq_norm hr.1).mp hr)
  refine ⟨hk, ?_⟩
  have hs : (eLpNorm (fun p : ℝ × ℝ => a p.1 * χ p * r p.2) 2
      (volume.prod volume)).toReal ^ 2 =
      ((eLpNorm a 2 volume).toReal * (eLpNorm r 2 volume).toReal) ^ 2 := by
    rw [l2_norm_sq hk]
    simp_rw [heq]
    rw [integral_prod_mul (fun x : ℝ => ‖a x‖ ^ 2) (fun ξ : ℝ => ‖r ξ‖ ^ 2),
      ← l2_norm_sq ha, ← l2_norm_sq hr, mul_pow]
  exact (sq_eq_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).mp hs

private theorem phase_fubini (χ : ℝ → ℝ → ℂ)
    (hχ : Continuous (fun p : ℝ × ℝ => χ p.1 p.2))
    (hχnorm : ∀ x ξ, ‖χ x ξ‖ = 1)
    (hχsub : ∀ x y ξ, χ (x - y) ξ = χ x ξ * star (χ y ξ))
    (m g : ℝ → ℂ) (hm : Integrable m) (hg : Integrable g) (x : ℝ) :
    (∫ ξ, m ξ * χ x ξ * (∫ y, star (χ y ξ) * g y)) =
      ∫ y, (∫ ξ, m ξ * χ (x - y) ξ) * g y := by
  have hc1 : Continuous (fun p : ℝ × ℝ => χ x p.1) :=
    hχ.comp (continuous_const.prodMk continuous_fst)
  have hc2 : Continuous (fun p : ℝ × ℝ => star (χ p.2 p.1)) :=
    (hχ.comp continuous_swap).star
  have hmeas := ((hm.1.comp_fst.mul hc1.aestronglyMeasurable).mul
    hc2.aestronglyMeasurable).mul hg.1.comp_snd
  have hf : Integrable (fun p : ℝ × ℝ =>
      m p.1 * χ x p.1 * star (χ p.2 p.1) * g p.2) (volume.prod volume) := by
    apply (hm.norm.mul_prod hg.norm).mono' hmeas
    filter_upwards [] with p
    change ‖m p.1 * χ x p.1 * star (χ p.2 p.1) * g p.2‖ ≤ ‖m p.1‖ * ‖g p.2‖
    simp only [norm_mul, norm_star, hχnorm, mul_one, le_refl]
  calc
    _ = ∫ ξ, ∫ y, m ξ * χ x ξ * star (χ y ξ) * g y := by
      simp only [mul_assoc, integral_const_mul]
    _ = ∫ y, ∫ ξ, m ξ * χ x ξ * star (χ y ξ) * g y := integral_integral_swap hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [hχsub]
      ring

theorem solution (a b m : ℝ → ℂ) (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) (hm : Integrable m volume) :
    let χ : ℝ → ℝ → ℂ := fun x ξ =>
      Complex.exp (((2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
    ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ u : Lp ℂ 2 (volume : Measure ℝ), ∀ᵐ x ∂volume,
        T u x = a x * ∫ ξ, m ξ * χ x ξ * (∫ y, star (χ y ξ) * b y * u y) ∧
        T u x = a x * ∫ y, (∫ ξ, m ξ * χ (x - y) ξ) * b y * u y) ∧
      IsNuclearOperator T ∧
      traceNorm T ≤ (eLpNorm a 2 volume).toReal * (eLpNorm b 2 volume).toReal *
        ∫ ξ, ‖m ξ‖ := by
  let χ : ℝ → ℝ → ℂ := fun x ξ =>
    Complex.exp (((2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
  change ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
    (∀ u : Lp ℂ 2 (volume : Measure ℝ), ∀ᵐ x ∂volume,
      T u x = a x * ∫ ξ, m ξ * χ x ξ * (∫ y, star (χ y ξ) * b y * u y) ∧
      T u x = a x * ∫ y, (∫ ξ, m ξ * χ (x - y) ξ) * b y * u y) ∧
    IsNuclearOperator T ∧ traceNorm T ≤
      (eLpNorm a 2 volume).toReal * (eLpNorm b 2 volume).toReal * ∫ ξ, ‖m ξ‖
  let r : ℝ → ℂ := fun ξ => (Real.sqrt ‖m ξ‖ : ℂ)
  let s : ℝ → ℂ := fun ξ => m ξ / r ξ
  have hrnorm (ξ : ℝ) : ‖r ξ‖ ^ 2 = ‖m ξ‖ := by
    simp only [r, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (norm_nonneg _)]
  have hsnorm (ξ : ℝ) : ‖s ξ‖ ^ 2 = ‖m ξ‖ := by
    by_cases hz : m ξ = 0
    · simp [s, r, hz]
    · have hn : ‖m ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      change ‖m ξ / r ξ‖ ^ 2 = _
      rw [norm_div, div_pow, hrnorm]
      field_simp [hn]
  have hrs (ξ : ℝ) : r ξ * s ξ = m ξ := by
    by_cases hz : m ξ = 0
    · simp [r, s, hz]
    · have hrz : r ξ ≠ 0 := by
        intro h
        have hmn : ‖m ξ‖ = 0 := by simpa [h] using (hrnorm ξ).symm
        exact hz (norm_eq_zero.mp hmn)
      dsimp only [s]
      field_simp [hrz]
  have hrmeas : AEStronglyMeasurable r volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable hm.1.norm)
  have hsmeas : AEStronglyMeasurable s volume := hm.1.div₀ hrmeas
  have hr : MemLp r 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hrmeas).mpr
    simpa only [hrnorm] using hm.norm
  have hs : MemLp s 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hsmeas).mpr
    simpa only [hsnorm] using hm.norm
  have hmassr : (eLpNorm r 2 volume).toReal ^ 2 = ∫ ξ, ‖m ξ‖ := by
    rw [l2_norm_sq hr]
    simp_rw [hrnorm]
  have hmasss : (eLpNorm s 2 volume).toReal ^ 2 = ∫ ξ, ‖m ξ‖ := by
    rw [l2_norm_sq hs]
    simp_rw [hsnorm]
  have hsame : (eLpNorm r 2 volume).toReal = (eLpNorm s 2 volume).toReal :=
    (sq_eq_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp (hmassr.trans hmasss.symm)
  have hmass : (eLpNorm r 2 volume).toReal * (eLpNorm s 2 volume).toReal =
      ∫ ξ, ‖m ξ‖ := by rw [← hsame, ← pow_two, hmassr]
  have hχcont : Continuous (fun p : ℝ × ℝ => χ p.1 p.2) := by
    dsimp only [χ]
    fun_prop
  have hχnorm (x ξ : ℝ) : ‖χ x ξ‖ = 1 := by
    simp [χ, Complex.norm_exp]
  have hχsub (x y ξ : ℝ) : χ (x - y) ξ = χ x ξ * star (χ y ξ) := by
    simp only [χ, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  let k : ℝ → ℝ → ℂ := fun x ξ => a x * χ x ξ * r ξ
  let l : ℝ → ℝ → ℂ := fun ξ y => s ξ * star (χ y ξ) * b y
  obtain ⟨hk, hknorm⟩ := unit_phase_kernel a r (fun p => χ p.1 p.2) ha hr
    hχcont.aestronglyMeasurable (fun p => hχnorm p.1 p.2)
  have hχstar : Continuous (fun p : ℝ × ℝ => star (χ p.2 p.1)) :=
    (hχcont.comp continuous_swap).star
  obtain ⟨hl, hlnorm⟩ := unit_phase_kernel s b (fun p => star (χ p.2 p.1)) hs hb
    hχstar.aestronglyMeasurable (fun p => by rw [norm_star, hχnorm])
  obtain ⟨T, hT, hnuc, hnorm⟩ := L2_kernel_composition_nuclear volume k l hk hl
  refine ⟨T, ?_, hnuc, ?_⟩
  · intro u
    filter_upwards [hT u] with x hx
    have hfreq : T u x = a x *
        ∫ ξ, m ξ * χ x ξ * (∫ y, star (χ y ξ) * b y * u y) := by
      rw [hx, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp only [k, l]
      simp only [mul_assoc, integral_const_mul]
      rw [← hrs ξ]
      ring
    refine ⟨hfreq, ?_⟩
    have hbu : Integrable (fun y => b y * u y) :=
      memLp_one_iff_integrable.mp ((Lp.memLp u).mul hb)
    have hswap := phase_fubini χ hχcont hχnorm hχsub m (fun y => b y * u y) hm hbu x
    exact hfreq.trans (by simpa only [mul_assoc] using congrArg (fun z => a x * z) hswap)
  · rw [hknorm, hlnorm] at hnorm
    calc
      traceNorm T ≤ ((eLpNorm a 2 volume).toReal * (eLpNorm r 2 volume).toReal) *
          ((eLpNorm s 2 volume).toReal * (eLpNorm b 2 volume).toReal) := hnorm
      _ = ((eLpNorm a 2 volume).toReal * (eLpNorm b 2 volume).toReal) *
          ((eLpNorm r 2 volume).toReal * (eLpNorm s 2 volume).toReal) := by ring
      _ = _ := by rw [hmass]

#print axioms solution
