-- Prove2me | solution 1 for IDivGeom.ExpFam.eq_2_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:13:37.042047+00:00
-- url     : https://prove2.me/submissions/380f99dd-6338-4393-8067-4b159fbbfd73

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

set_option autoImplicit false

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam.ParallelogramProof

/-- `z · klFun (w / z) = w log w − w log z + z − w` for `z > 0`, `w ≥ 0`. -/
theorem mul_klFun_div (z w : ℝ) (hz : 0 < z) (hw : 0 ≤ w) :
    z * klFun (w / z) = w * Real.log w - w * Real.log z + z - w := by
  have hzw : z * (w / z) = w := by field_simp
  rw [klFun_apply]
  rcases eq_or_lt_of_le hw with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hz.ne',
      show z * (w / z * (Real.log w - Real.log z) + 1 - w / z)
        = (z * (w / z)) * (Real.log w - Real.log z) + z - z * (w / z) by ring, hzw]
    ring

/-- The pointwise parallelogram identity for `klFun x = x log x + 1 - x`, with `z = (x + y)/2`
and `u z = x`, `v z = y`. -/
theorem klFun_parallelogram (x y u v : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hu : u * ((x + y) / 2) = x) (hv : v * ((x + y) / 2) = y) :
    klFun x + klFun y
      = 2 * klFun ((x + y) / 2) + (x + y) / 2 * klFun u + (x + y) / 2 * klFun v := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (x + y) / 2 by positivity) with hz0 | hzpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst hx0 hy0
    simp [klFun_zero]
    norm_num
  · have hzne : (x + y) / 2 ≠ 0 := hzpos.ne'
    have hux : u = x / ((x + y) / 2) := eq_div_of_mul_eq hzne hu
    have hvy : v = y / ((x + y) / 2) := eq_div_of_mul_eq hzne hv
    rw [hux, hvy, mul_klFun_div _ x hzpos hx, mul_klFun_div _ y hzpos hy, klFun_apply,
      klFun_apply, klFun_apply]
    ring

end IDivGeom.ExpFam.ParallelogramProof

open IDivGeom.ExpFam.ParallelogramProof

theorem solution {X : Type*} [MeasurableSpace X]
    (P P' R : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [IsProbabilityMeasure R] (hP : klDiv P R ≠ ⊤) (hP' : klDiv P' R ≠ ⊤) :
    klDiv P R + klDiv P' R =
      2 * klDiv ((1 / 2 : ℝ≥0∞) • (P + P')) R
        + klDiv P ((1 / 2 : ℝ≥0∞) • (P + P'))
        + klDiv P' ((1 / 2 : ℝ≥0∞) • (P + P')) := by
  have hPR : P ≪ R := (klDiv_ne_top_iff.mp hP).1
  have hP'R : P' ≪ R := (klDiv_ne_top_iff.mp hP').1
  -- The mixture, rewritten with an `ℝ≥0` scalar.
  have hMeq : (1 / 2 : ℝ≥0∞) • (P + P') = (1 / 2 : ℝ≥0) • (P + P') := by
    ext s _
    simp [ENNReal.smul_def]
  rw [hMeq]
  set M : Measure X := (1 / 2 : ℝ≥0) • (P + P') with hMdef
  have hMR : M ≪ R := (hPR.add_left hP'R).smul_left _
  have hPM : P ≪ M := by
    intro s hs
    rw [hMdef, Measure.smul_apply, Measure.add_apply] at hs
    simp at hs
    exact hs.1
  have hP'M : P' ≪ M := by
    intro s hs
    rw [hMdef, Measure.smul_apply, Measure.add_apply] at hs
    simp at hs
    exact hs.2
  -- Densities with respect to `R`.
  have hm : ∀ᵐ ω ∂ R, M.rnDeriv R ω = (1 / 2 : ℝ≥0) • (P.rnDeriv R ω + P'.rnDeriv R ω) := by
    filter_upwards [Measure.rnDeriv_smul_left' (P + P') R (1 / 2),
      Measure.rnDeriv_add' P P' R] with ω h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.add_apply]
  have hchP := Measure.rnDeriv_mul_rnDeriv (κ := R) hPM
  have hchP' := Measure.rnDeriv_mul_rnDeriv (κ := R) hP'M
  -- Express every divergence as a lower integral against `R`.
  rw [klDiv_eq_lintegral_klFun_of_ac hPR, klDiv_eq_lintegral_klFun_of_ac hP'R,
    klDiv_eq_lintegral_klFun_of_ac hMR, klDiv_eq_lintegral_klFun_of_ac hPM,
    klDiv_eq_lintegral_klFun_of_ac hP'M,
    ← lintegral_rnDeriv_mul hMR (by fun_prop), ← lintegral_rnDeriv_mul hMR (by fun_prop)]
  rw [← lintegral_add_left (by fun_prop), ← lintegral_const_mul _ (by fun_prop),
    ← lintegral_add_left (by fun_prop), ← lintegral_add_left (by fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [hm, hchP, hchP', Measure.rnDeriv_lt_top P R, Measure.rnDeriv_lt_top P' R]
    with ω hmω hcP hcP' hpt hp't
  simp only [Pi.mul_apply] at hcP hcP'
  -- Real-valued densities.
  have hpne : P.rnDeriv R ω ≠ ⊤ := hpt.ne
  have hp'ne : P'.rnDeriv R ω ≠ ⊤ := hp't.ne
  have hmne : M.rnDeriv R ω ≠ ⊤ := by
    rw [hmω]
    exact ENNReal.nnreal_smul_ne_top (ENNReal.add_ne_top.mpr ⟨hpne, hp'ne⟩)
  have hz : (M.rnDeriv R ω).toReal
      = ((P.rnDeriv R ω).toReal + (P'.rnDeriv R ω).toReal) / 2 := by
    rw [hmω, ENNReal.toReal_smul, ENNReal.toReal_add hpne hp'ne]
    simp only [NNReal.smul_def, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, smul_eq_mul]
    ring
  have hu : (P.rnDeriv M ω).toReal * (M.rnDeriv R ω).toReal = (P.rnDeriv R ω).toReal := by
    rw [← ENNReal.toReal_mul, hcP]
  have hv : (P'.rnDeriv M ω).toReal * (M.rnDeriv R ω).toReal = (P'.rnDeriv R ω).toReal := by
    rw [← ENNReal.toReal_mul, hcP']
  rw [hz] at hu hv
  have hid := klFun_parallelogram _ _ _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hu hv
  have hmofReal : M.rnDeriv R ω = ENNReal.ofReal (M.rnDeriv R ω).toReal :=
    (ENNReal.ofReal_toReal hmne).symm
  have hk : ∀ w : ℝ, 0 ≤ w → 0 ≤ klFun w := fun w hw => klFun_nonneg hw
  have hz0 : 0 ≤ ((P.rnDeriv R ω).toReal + (P'.rnDeriv R ω).toReal) / 2 := by positivity
  have h2c : 0 ≤ 2 * klFun (((P.rnDeriv R ω).toReal + (P'.rnDeriv R ω).toReal) / 2) :=
    mul_nonneg (by norm_num) (hk _ hz0)
  have hd : 0 ≤ ((P.rnDeriv R ω).toReal + (P'.rnDeriv R ω).toReal) / 2
      * klFun (P.rnDeriv M ω).toReal := mul_nonneg hz0 (hk _ ENNReal.toReal_nonneg)
  rw [hmofReal, hz, ENNReal.toReal_ofReal hz0,
    ← ENNReal.ofReal_add (hk _ ENNReal.toReal_nonneg) (hk _ ENNReal.toReal_nonneg),
    ← ENNReal.ofReal_mul hz0, ← ENNReal.ofReal_mul hz0,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add h2c hd,
    ← ENNReal.ofReal_add (add_nonneg h2c hd) (mul_nonneg hz0 (hk _ ENNReal.toReal_nonneg)), hid]
