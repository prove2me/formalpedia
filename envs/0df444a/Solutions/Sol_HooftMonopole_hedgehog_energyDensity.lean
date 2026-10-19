-- Prove2me | solution 1 for HooftMonopole.hedgehog_energyDensity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:47:48.286516+00:00
-- url     : https://prove2.me/submissions/6d43740a-8454-4f89-a3fc-e8c6108de71d

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

open HooftMonopole in
theorem solution (e lam F : ℝ) (q w : ℝ → ℝ) (x : Space) (hx : x ≠ 0)
    (hq : DifferentiableAt ℝ q ‖x‖) (hw : DifferentiableAt ℝ w ‖x‖) :
    energyDensity e lam F (hedgehogHiggs q) (hedgehogGauge w) x =
      radialEnergyIntegrand e lam F w q ‖x‖ :=
  HMA.energy_formula e lam F q w x hx hq hw
