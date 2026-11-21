-- Prove2me | solution 1 for MasulloAudit.mellin_poisson_orbital_trace
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:24:30.011344+00:00
-- url     : https://prove2.me/submissions/dbbef011-6086-49f2-b0e5-c9aa89cfe68f

import Mathlib

open Real Complex MeasureTheory Set
open scoped FourierTransform ContDiff

theorem solution (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hpos : tsupport φ ⊆ Set.Ioi 0) (p : ℝ) (hp : 1 < p) :
    Summable (fun k : ℤ => mellin φ (2 * π * I * k / Real.log p)) ∧
    ∑' k : ℤ, mellin φ (2 * π * I * k / Real.log p) =
      (Real.log p : ℂ) * ∑' n : ℤ, φ (p ^ n) := by
  set L := Real.log p with hLdef
  have hL : 0 < L := Real.log_pos hp
  -- the rescaled pulled-back function h(v) = φ(exp(-L v))
  set h : ℝ → ℂ := fun v => φ (Real.exp (-(L * v))) with hhdef
  have hh_smooth : ContDiff ℝ ∞ h :=
    hφ.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)
  have hh_supp : HasCompactSupport h := by
    have hK : IsCompact ((fun t => -Real.log t / L) '' tsupport φ) := by
      refine hc.isCompact.image_of_continuousOn ?_
      refine ContinuousOn.div_const (ContinuousOn.neg ?_) _
      exact Real.continuousOn_log.mono fun t ht => (ne_of_gt (hpos ht))
    refine HasCompactSupport.intro hK fun v hv => ?_
    by_contra hne
    apply hv
    refine ⟨Real.exp (-(L * v)), subset_tsupport _ hne, ?_⟩
    simp only [Real.log_exp]
    field_simp
  let F : SchwartzMap ℝ ℂ := hh_supp.toSchwartzMap hh_smooth
  have hF : ∀ v, F v = h v := fun v => rfl
  -- Fourier transform of h at integers is a rescaled Mellin transform
  have hFour : ∀ k : ℤ, 𝓕 (h) (k : ℝ) = (L : ℂ)⁻¹ * mellin φ (2 * π * I * k / L) := by
    intro k
    have h1 := mellin_eq_fourier (fun t => φ (t ^ L)) (s := 2 * π * I * k)
    have h2 := mellin_comp_rpow φ (2 * π * I * k) L
    have hre : (2 * π * I * (k : ℂ)).re = 0 := by simp
    have him : (2 * π * I * (k : ℂ)).im / (2 * π) = k := by
      simp
    rw [hre, him] at h1
    have hfun : (fun u : ℝ => Real.exp (-0 * u) • φ (Real.exp (-u) ^ L)) = h := by
      funext u
      simp only [neg_zero, zero_mul, Real.exp_zero, one_smul, hhdef]
      rw [← Real.exp_mul]; congr 2; ring
    rw [hfun] at h1
    rw [← h1, h2, abs_of_pos hL, Complex.real_smul]
    push_cast; ring_nf
  have hPoisson := SchwartzMap.tsum_eq_tsum_fourier F 0
  simp only [zero_add, hF, SchwartzMap.fourier_coe] at hPoisson
  have hsumF : Summable fun k : ℤ => 𝓕 F (k : ℝ) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 F).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  simp only [SchwartzMap.fourier_coe] at hsumF
  have hcoe : (F : ℝ → ℂ) = h := rfl
  rw [hcoe] at hsumF hPoisson
  have hfour0 : ∀ k : ℤ, fourier k ((0 : ℝ) : UnitAddCircle) = 1 := by
    intro k; simp
  simp only [hfour0, mul_one, hFour] at hPoisson hsumF
  have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hsum : Summable (fun k : ℤ => mellin φ (2 * π * I * k / L)) := by
    have := hsumF.mul_left (L : ℂ)
    refine this.congr fun k => ?_
    field_simp
  refine ⟨hsum, ?_⟩
  have hlhs : ∑' n : ℤ, h n = ∑' n : ℤ, φ (p ^ n) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hhdef, Equiv.neg_apply]
    congr 1
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by linarith)]
    congr 1; push_cast; ring
  rw [hlhs, tsum_mul_left] at hPoisson
  rw [hPoisson]
  field_simp
