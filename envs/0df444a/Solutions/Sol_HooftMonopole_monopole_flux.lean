-- Prove2me | solution 1 for HooftMonopole.monopole_flux
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:54:09.868782+00:00
-- url     : https://prove2.me/submissions/4eaa86cb-f89c-4a6a-89c5-0f6d0181087a

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

namespace HMB
open HooftMonopole HMA

lemma dq (F : ℝ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (fun r : ℝ => F / r) (-F / r ^ 2) r := by
  have h := (hasDerivAt_inv hr).const_mul F
  have e1 : (fun r : ℝ => F / r) = fun y => F * y⁻¹ := by funext y; ring
  rw [e1]; exact h.congr_deriv (by field_simp)

lemma dw (e : ℝ) {r : ℝ} (hr : r ≠ 0) (he : e ≠ 0) :
    HasDerivAt (fun r : ℝ => -1 / (e * r ^ 2)) (2 / (e * r ^ 3)) r := by
  have h1 : HasDerivAt (fun r : ℝ => e * r ^ 2) (e * (2 * r)) r := by
    simpa using (hasDerivAt_pow 2 r).const_mul e
  have h2 := h1.inv (by positivity)
  have h3 := h2.const_mul (-1 : ℝ)
  have e1 : (fun r : ℝ => -1 / (e * r ^ 2)) = fun y => -1 * (fun r : ℝ => e * r ^ 2)⁻¹ y := by
    funext y; simp [div_eq_mul_inv]
  rw [e1]; exact h3.congr_deriv (by field_simp)

theorem main (e F : ℝ) (he : 0 < e) (hF : 0 < F) (x : Space) (hx : x ≠ 0) :
    (∀ i a : Fin 3,
      covDeriv e (hedgehogHiggs (fun r => F / r)) (hedgehogGauge (fun r => -1 / (e * r ^ 2)))
        i x a = 0) ∧
    (∀ i j : Fin 3,
      ∑ a, hedgehogHiggs (fun r => F / r) x a *
          fieldStrength e (hedgehogGauge (fun r => -1 / (e * r ^ 2))) i j x a =
        -(F / (e * ‖x‖ ^ 3)) * ∑ a, levi i j a * x a) ∧
    (∀ i j : Fin 3,
      emField e (hedgehogHiggs (fun r => F / r)) (hedgehogGauge (fun r => -1 / (e * r ^ 2)))
          i j x =
        -(1 / (e * ‖x‖ ^ 3)) * ∑ a, levi i j a * x a) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs := norm_sq3 x
  have hq := dq F hr
  have hw := dw e hr he.ne'
  have hcov : ∀ i a : Fin 3,
      covDeriv e (hedgehogHiggs (fun r => F / r)) (hedgehogGauge (fun r => -1 / (e * r ^ 2)))
        i x a = 0 := by
    intro i a
    rw [cov_formula e x hx _ _ hq.differentiableAt, hq.deriv, ← hs]
    have h1 : F / ‖x‖ + e * (-1 / (e * ‖x‖ ^ 2)) * (F / ‖x‖) * ‖x‖ ^ 2 = 0 := by
      field_simp; ring
    have h2 : -F / ‖x‖ ^ 2 / ‖x‖ - e * (-1 / (e * ‖x‖ ^ 2)) * (F / ‖x‖) = 0 := by
      field_simp; ring
    rw [h1, h2]; simp
  have hG : ∀ i j : Fin 3,
      ∑ a, hedgehogHiggs (fun r => F / r) x a *
          fieldStrength e (hedgehogGauge (fun r => -1 / (e * r ^ 2))) i j x a =
        -(F / (e * ‖x‖ ^ 3)) * ∑ a, levi i j a * x a := by
    intro i j
    simp only [field_formula e x hx _ hw.differentiableAt, hw.deriv, higgs_apply]
    rw [← hs]
    have hA : 2 * (-1 / (e * ‖x‖ ^ 2)) + 2 / (e * ‖x‖ ^ 3) * ‖x‖ ^ 2 / ‖x‖ = 0 := by
      field_simp; ring
    have hB : e * (-1 / (e * ‖x‖ ^ 2)) ^ 2 - 2 / (e * ‖x‖ ^ 3) / ‖x‖ = -1 / (e * ‖x‖ ^ 4) := by
      field_simp; ring
    rw [hA, hB]
    simp only [mul_zero, zero_add]
    have : ∀ a : Fin 3, F / ‖x‖ * x a * (x a * (∑ k, levi i j k * x k) * (-1 / (e * ‖x‖ ^ 4))) =
        (x a ^ 2) * (-(F / (e * ‖x‖ ^ 5)) * ∑ k, levi i j k * x k) := by
      intro a; field_simp
    simp only [this, ← Finset.sum_mul]
    have h3 : ∑ a : Fin 3, x a ^ 2 = ‖x‖ ^ 2 := by rw [hs]; simp [Fin.sum_univ_three]
    rw [h3]
    field_simp
  refine ⟨hcov, hG, fun i j => ?_⟩
  unfold emField
  simp only [hcov, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [hG]
  have hN : higgsNormSq (hedgehogHiggs (fun r => F / r)) x = F ^ 2 := by
    unfold higgsNormSq
    simp only [higgs_apply]
    have : ∑ a : Fin 3, (F / ‖x‖ * x a) ^ 2 = F ^ 2 / ‖x‖ ^ 2 * ∑ a : Fin 3, x a ^ 2 := by
      rw [Finset.mul_sum]; congr 1; ext a; field_simp
    rw [this, show ∑ a : Fin 3, x a ^ 2 = ‖x‖ ^ 2 by rw [hs]; simp [Fin.sum_univ_three]]
    field_simp
  rw [hN, Real.sqrt_sq hF.le]
  field_simp

end HMB

namespace HMC
open HooftMonopole HMA MeasureTheory Real

lemma sphere_univ : ((volume : Measure Space).toSphere).real Set.univ = 4 * π := by
  rw [measureReal_def, Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp; ring

theorem main (e F : ℝ) (he : 0 < e) (hF : 0 < F) (R : ℝ) (hR : 0 < R) :
    |R ^ 2 * ∫ ω : Metric.sphere (0 : Space) 1,
        ∑ k, magneticField e (hedgehogHiggs (fun r => F / r))
            (hedgehogGauge (fun r => -1 / (e * r ^ 2))) (R • (ω : Space)) k * (ω : Space) k
        ∂(volume : Measure Space).toSphere| = 4 * π / e := by
  have hconst : ∀ ω : Metric.sphere (0 : Space) 1,
      ∑ k, magneticField e (hedgehogHiggs (fun r => F / r))
            (hedgehogGauge (fun r => -1 / (e * r ^ 2))) (R • (ω : Space)) k * (ω : Space) k =
        -(1 / (e * R ^ 2)) := by
    intro ω
    have hω : ‖(ω : Space)‖ = 1 := by simp
    have hy : R • (ω : Space) ≠ 0 := by
      intro h
      have := congrArg norm h
      rw [norm_smul, hω, Real.norm_eq_abs, abs_of_pos hR] at this
      simp at this; linarith
    have hny : ‖R • (ω : Space)‖ = R := by rw [norm_smul, hω, Real.norm_eq_abs, abs_of_pos hR, mul_one]
    have h3 := (HMB.main e F he hF _ hy).2.2
    unfold magneticField
    simp only [h3, hny]
    have hs := norm_sq3 (ω : Space)
    rw [hω] at hs
    simp only [Fin.sum_univ_three, levi, PiLp.smul_apply, smul_eq_mul]
    norm_num
    field_simp
    linear_combination 2 * hs
  simp only [hconst, integral_const, smul_eq_mul, sphere_univ]
  rw [show R ^ 2 * (4 * π * -(1 / (e * R ^ 2))) = -(4 * π / e) by field_simp]
  rw [abs_neg, abs_of_pos (by positivity)]

end HMC

open HooftMonopole MeasureTheory Real in
theorem solution (e F : ℝ) (he : 0 < e) (hF : 0 < F) (R : ℝ) (hR : 0 < R) :
    |R ^ 2 * ∫ ω : Metric.sphere (0 : Space) 1,
        ∑ k, magneticField e (hedgehogHiggs (fun r => F / r))
            (hedgehogGauge (fun r => -1 / (e * r ^ 2))) (R • (ω : Space)) k * (ω : Space) k
        ∂(volume : Measure Space).toSphere| = 4 * π / e :=
  HMC.main e F he hF R hR
