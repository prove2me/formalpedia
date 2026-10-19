-- Prove2me | solution 1 for HooftMonopole.energy_dimensionless
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:56:12.570693+00:00
-- url     : https://prove2.me/submissions/c18cbd6c-fc09-467e-b4d9-a274c3fb5432

import Mathlib
import Definitions.Def_HooftMonopole_Defs

namespace HMA
open HooftMonopole

lemma norm_hasFDeriv (x : Space) (hx : x ≠ 0) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (fun y : Space => ‖y‖) L x ∧
      ∀ v : Space, L v = inner ℝ x v / ‖x‖ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 := (hasFDerivAt_id (𝕜 := ℝ) x).norm_sq.sqrt (by simpa using hn)
  refine ⟨_, h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_), fun v => ?_⟩
  · simp [Real.sqrt_sq (norm_nonneg y)]
  · simp only [id, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,
      Real.sqrt_sq (norm_nonneg x)]
    field_simp
    ring

lemma radial_hasFDeriv (x : Space) (hx : x ≠ 0) (q : ℝ → ℝ) (hq : DifferentiableAt ℝ q ‖x‖) :
    ∃ L : Space →L[ℝ] ℝ, HasFDerivAt (fun y : Space => q ‖y‖) L x ∧
      ∀ v : Space, L v = deriv q ‖x‖ * (inner ℝ x v / ‖x‖) := by
  obtain ⟨L, hL, hLv⟩ := norm_hasFDeriv x hx
  refine ⟨deriv q ‖x‖ • L, hq.hasDerivAt.comp_hasFDerivAt x hL, fun v => ?_⟩
  simp [hLv]

lemma higgs_pd (x : Space) (hx : x ≠ 0) (q : ℝ → ℝ) (hq : DifferentiableAt ℝ q ‖x‖)
    (j a : Fin 3) :
    partialDeriv (hedgehogHiggs q) j x a =
      deriv q ‖x‖ * (x j / ‖x‖) * x a + q ‖x‖ * (if a = j then 1 else 0) := by
  obtain ⟨L, hL, hLv⟩ := radial_hasFDeriv x hx q hq
  have h : HasFDerivAt (fun y : Space => q ‖y‖ • y)
      (q ‖x‖ • ContinuousLinearMap.id ℝ Space + L.smulRight x) x := hL.smul (hasFDerivAt_id x)
  unfold partialDeriv hedgehogHiggs
  rw [h.fderiv]
  simp [hLv, EuclideanSpace.inner_single_right]
  ring

lemma lin_hasFDeriv (x : Space) (c : Fin 3 → Fin 3 → ℝ) :
    ∃ M : Space →L[ℝ] Space,
      HasFDerivAt (fun y : Space => ∑ a, (∑ b, c a b * y b) • EuclideanSpace.single a (1 : ℝ)) M x ∧
      ∀ v : Space, M v = ∑ a, (∑ b, c a b * v b) • EuclideanSpace.single a (1 : ℝ) := by
  have hb : ∀ a : Fin 3, HasFDerivAt (fun y : Space => ∑ b, c a b * y b)
      (∑ b, c a b • (EuclideanSpace.proj b : Space →L[ℝ] ℝ)) x := by
    intro a
    have := HasFDerivAt.fun_sum (u := Finset.univ) (A := fun b (y : Space) => c a b * y b)
      (A' := fun b => c a b • (EuclideanSpace.proj b : Space →L[ℝ] ℝ)) (x := x)
      (fun b _ => ((EuclideanSpace.proj b : Space →L[ℝ] ℝ).hasFDerivAt).const_mul (c a b))
    simpa using this
  have := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun a (y : Space) => (∑ b, c a b * y b) • EuclideanSpace.single a (1 : ℝ))
    (A' := fun a => (∑ b, c a b • (EuclideanSpace.proj b : Space →L[ℝ] ℝ)).smulRight
      (EuclideanSpace.single a (1 : ℝ))) (x := x)
    (fun a _ => (hb a).smul_const _)
  refine ⟨_, this, fun v => ?_⟩
  simp

lemma gauge_apply (w : ℝ → ℝ) (i : Fin 3) (x : Space) (a : Fin 3) :
    hedgehogGauge w i x a = w ‖x‖ * ∑ b, levi i a b * x b := by
  simp only [hedgehogGauge, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq]

lemma gauge_pd (x : Space) (hx : x ≠ 0) (w : ℝ → ℝ) (hw : DifferentiableAt ℝ w ‖x‖)
    (i j a : Fin 3) :
    partialDeriv (hedgehogGauge w i) j x a =
      deriv w ‖x‖ * (x j / ‖x‖) * (∑ b, levi i a b * x b) + w ‖x‖ * levi i a j := by
  obtain ⟨L, hL, hLv⟩ := radial_hasFDeriv x hx w hw
  obtain ⟨M, hM, hMv⟩ := lin_hasFDeriv x (fun a b => levi i a b)
  have h : HasFDerivAt (fun y : Space => w ‖y‖ •
      ∑ a, (∑ b, levi i a b * y b) • EuclideanSpace.single a (1 : ℝ))
      (w ‖x‖ • M + L.smulRight (∑ a, (∑ b, levi i a b * x b) • EuclideanSpace.single a (1 : ℝ))) x :=
    hL.smul hM
  unfold partialDeriv hedgehogGauge
  rw [h.fderiv]
  simp [hLv, hMv, EuclideanSpace.inner_single_right, Finset.sum_apply, Pi.single_apply]
  ring

lemma higgs_apply (q : ℝ → ℝ) (x : Space) (a : Fin 3) :
    hedgehogHiggs q x a = q ‖x‖ * x a := by
  simp [hedgehogHiggs]

lemma cov_formula (e : ℝ) (x : Space) (hx : x ≠ 0) (q w : ℝ → ℝ) (hq : DifferentiableAt ℝ q ‖x‖)
    (i a : Fin 3) :
    covDeriv e (hedgehogHiggs q) (hedgehogGauge w) i x a =
      (if i = a then q ‖x‖ + e * w ‖x‖ * q ‖x‖ * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) else 0) +
        (deriv q ‖x‖ / ‖x‖ - e * w ‖x‖ * q ‖x‖) * x i * x a := by
  unfold covDeriv
  rw [higgs_pd x hx q hq]
  simp only [gauge_apply, higgs_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases a <;> simp [levi] <;> ring

lemma field_formula (e : ℝ) (x : Space) (hx : x ≠ 0) (w : ℝ → ℝ) (hw : DifferentiableAt ℝ w ‖x‖)
    (i j a : Fin 3) :
    fieldStrength e (hedgehogGauge w) i j x a =
      levi a i j * (2 * w ‖x‖ + deriv w ‖x‖ * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / ‖x‖) +
        x a * (∑ k, levi i j k * x k) * (e * w ‖x‖ ^ 2 - deriv w ‖x‖ / ‖x‖) := by
  unfold fieldStrength
  rw [gauge_pd x hx w hw, gauge_pd x hx w hw]
  simp only [gauge_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> (simp [levi]; try ring_nf) <;> simp

lemma sumG (x : Space) (A B : ℝ) :
    ∑ i, ∑ j, ∑ a, (levi a i j * A + x a * (∑ k, levi i j k * x k) * B) ^ 2 =
      6 * A ^ 2 + 4 * A * B * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) +
        2 * B ^ 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ 2 := by
  simp [Fin.sum_univ_three, levi]; ring

lemma sumD (x : Space) (α β : ℝ) :
    ∑ i : Fin 3, ∑ a : Fin 3, ((if i = a then α else 0) + β * x i * x a) ^ 2 =
      3 * α ^ 2 + 2 * α * β * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) +
        β ^ 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ 2 := by
  simp [Fin.sum_univ_three]; ring

lemma norm_sq3 (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three]

theorem energy_formula (e lam F : ℝ) (q w : ℝ → ℝ) (x : Space) (hx : x ≠ 0)
    (hq : DifferentiableAt ℝ q ‖x‖) (hw : DifferentiableAt ℝ w ‖x‖) :
    energyDensity e lam F (hedgehogHiggs q) (hedgehogGauge w) x =
      radialEnergyIntegrand e lam F w q ‖x‖ := by
  unfold energyDensity higgsNormSq
  simp only [field_formula e x hx w hw, cov_formula e x hx q w hq, higgs_apply]
  rw [sumG, sumD]
  have hs : ∑ a : Fin 3, (q ‖x‖ * x a) ^ 2 = q ‖x‖ ^ 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
    simp [Fin.sum_univ_three]; ring
  rw [hs, ← norm_sq3]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  unfold radialEnergyIntegrand
  field_simp
  ring

end HMA

namespace HMD
open HooftMonopole HMA MeasureTheory Real Set

lemma ball_real : (volume : Measure Space).real (Metric.ball 0 1) = 4 * π / 3 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]; ring

lemma rad_scale (e lam F : ℝ) (he : 0 < e) (hF : 0 < F) (q w : ℝ → ℝ)
    (hq : DifferentiableOn ℝ q (Ioi 0)) (hw : DifferentiableOn ℝ w (Ioi 0)) (y : ℝ) (hy : 0 < y) :
    (e * F * y) ^ 2 * radialEnergyIntegrand 1 (lam / e ^ 2) 1
        (fun s => w (s / (e * F)) / (F ^ 2 * e)) (fun s => q (s / (e * F)) / (F ^ 2 * e)) (e * F * y) =
      y ^ 2 * radialEnergyIntegrand e lam F w q y / F ^ 2 := by
  have hc : 0 < e * F := mul_pos he hF
  have hyy : e * F * y / (e * F) = y := by field_simp
  have hdw : HasDerivAt (fun s => w (s / (e * F)) / (F ^ 2 * e))
      (deriv w y * (1 / (e * F)) / (F ^ 2 * e)) (e * F * y) := by
    have h1 : HasDerivAt (fun s : ℝ => s / (e * F)) (1 / (e * F)) (e * F * y) := by
      simpa using (hasDerivAt_id (e * F * y)).div_const (e * F)
    have h2 : HasDerivAt w (deriv w y) (e * F * y / (e * F)) := by
      rw [hyy]; exact (hw.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
    exact (HasDerivAt.comp (e * F * y) h2 h1).div_const _
  have hdq : HasDerivAt (fun s => q (s / (e * F)) / (F ^ 2 * e))
      (deriv q y * (1 / (e * F)) / (F ^ 2 * e)) (e * F * y) := by
    have h1 : HasDerivAt (fun s : ℝ => s / (e * F)) (1 / (e * F)) (e * F * y) := by
      simpa using (hasDerivAt_id (e * F * y)).div_const (e * F)
    have h2 : HasDerivAt q (deriv q y) (e * F * y / (e * F)) := by
      rw [hyy]; exact (hq.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
    exact (HasDerivAt.comp (e * F * y) h2 h1).div_const _
  unfold radialEnergyIntegrand
  rw [hdw.deriv, hdq.deriv]
  simp only [hyy]
  field_simp

theorem main (e lam F : ℝ) (he : 0 < e) (hF : 0 < F) (q w : ℝ → ℝ)
    (hq : DifferentiableOn ℝ q (Set.Ioi 0)) (hw : DifferentiableOn ℝ w (Set.Ioi 0)) :
    energy e lam F (hedgehogHiggs q) (hedgehogGauge w) =
      4 * π * (e * F) / e ^ 2 *
        ∫ s in Set.Ioi (0 : ℝ), s ^ 2 *
          radialEnergyIntegrand 1 (lam / e ^ 2) 1
            (fun s => w (s / (e * F)) / (F ^ 2 * e)) (fun s => q (s / (e * F)) / (F ^ 2 * e)) s := by
  have hc : 0 < e * F := mul_pos he hF
  -- step 1: energy density is radial a.e.
  have h1 : energy e lam F (hedgehogHiggs q) (hedgehogGauge w) =
      ∫ x : Space, radialEnergyIntegrand e lam F w q ‖x‖ := by
    unfold energy
    apply integral_congr_ae
    have : ∀ᵐ x : Space, x ≠ 0 := by
      have := measure_singleton (μ := (volume : Measure Space)) 0
      exact (ae_iff.mpr (by simpa using this))
    filter_upwards [this] with x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    exact energy_formula e lam F q w x hx (hq.differentiableAt (Ioi_mem_nhds hx0))
      (hw.differentiableAt (Ioi_mem_nhds hx0))
  rw [h1, integral_fun_norm_addHaar (volume : Measure Space) (fun r => radialEnergyIntegrand e lam F w q r),
    ball_real]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  -- step 2: scaling on the right-hand side
  have h2 := integral_comp_mul_left_Ioi (fun s => s ^ 2 *
          radialEnergyIntegrand 1 (lam / e ^ 2) 1
            (fun s => w (s / (e * F)) / (F ^ 2 * e)) (fun s => q (s / (e * F)) / (F ^ 2 * e)) s) 0 hc
  rw [mul_zero] at h2
  have h3 : ∫ x in Ioi (0 : ℝ), (fun s => s ^ 2 *
          radialEnergyIntegrand 1 (lam / e ^ 2) 1
            (fun s => w (s / (e * F)) / (F ^ 2 * e)) (fun s => q (s / (e * F)) / (F ^ 2 * e)) s) (e * F * x) =
      ∫ y in Ioi (0 : ℝ), y ^ 2 * radialEnergyIntegrand e lam F w q y / F ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact rad_scale e lam F he hF q w hq hw y hy
  rw [h3, smul_eq_mul] at h2
  have h4 : ∫ s in Ioi (0 : ℝ), s ^ 2 *
          radialEnergyIntegrand 1 (lam / e ^ 2) 1
            (fun s => w (s / (e * F)) / (F ^ 2 * e)) (fun s => q (s / (e * F)) / (F ^ 2 * e)) s =
      (e * F) * ∫ y in Ioi (0 : ℝ), y ^ 2 * radialEnergyIntegrand e lam F w q y / F ^ 2 := by
    rw [h2]; field_simp
  rw [h4, integral_div]
  norm_num
  field_simp

end HMD

open HooftMonopole MeasureTheory Real in
theorem solution (e lam F : ℝ) (he : 0 < e) (hF : 0 < F) (q w : ℝ → ℝ)
    (hq : DifferentiableOn ℝ q (Set.Ioi 0)) (hw : DifferentiableOn ℝ w (Set.Ioi 0)) :
    energy e lam F (hedgehogHiggs q) (hedgehogGauge w) =
      4 * π * (e * F) / e ^ 2 *
        ∫ s in Set.Ioi (0 : ℝ), s ^ 2 *
          radialEnergyIntegrand 1 (lam / e ^ 2) 1
            (fun s => w (s / (e * F)) / (F ^ 2 * e)) (fun s => q (s / (e * F)) / (F ^ 2 * e)) s :=
  HMD.main e lam F he hF q w hq hw
