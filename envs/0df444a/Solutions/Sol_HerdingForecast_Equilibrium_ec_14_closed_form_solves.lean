-- Prove2me | solution 1 for HerdingForecast.Equilibrium.ec_14_closed_form_solves
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:32:04.650925+00:00
-- url     : https://prove2.me/submissions/6b32ccd0-f979-4499-87cc-3b936f0a4075

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model
import Theorems.Thm_HerdingForecast_Equilibrium_eq_3_posterior

open HerdingForecast.Equilibrium MeasureTheory ProbabilityTheory

lemma herd14_int (μ c0 c1 c2 : ℝ) (v : NNReal) :
    Integrable (fun θ : ℝ => c0 + c1 * θ + c2 * θ ^ 2) (gaussianReal μ v) := by
  have hi1 : Integrable (fun θ : ℝ => θ) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable le_rfl
  have hi2 : Integrable (fun θ : ℝ => θ ^ 2) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 2).integrable_sq
  exact ((integrable_const c0).add (hi1.const_mul c1)).add (hi2.const_mul c2)

lemma herd14_poly (μ c0 c1 c2 : ℝ) (v : NNReal) :
    ∫ θ, (c0 + c1 * θ + c2 * θ ^ 2) ∂gaussianReal μ v = c0 + c1 * μ + c2 * (μ ^ 2 + v) := by
  have hi1 : Integrable (fun θ : ℝ => θ) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable le_rfl
  have hi2 : Integrable (fun θ : ℝ => θ ^ 2) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 2).integrable_sq
  have hvar : ∫ θ, (θ - μ) ^ 2 ∂gaussianReal μ v = v := by
    have := variance_fun_id_gaussianReal (μ := μ) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable] at this
    simpa only [integral_id_gaussianReal] using this
  have hsq : ∫ θ, θ ^ 2 ∂gaussianReal μ v = μ ^ 2 + v := by
    have hi3 : Integrable (fun θ : ℝ => (θ - μ) ^ 2 + (2 * μ * θ - μ ^ 2)) (gaussianReal μ v) := by
      have : (fun θ : ℝ => (θ - μ) ^ 2 + (2 * μ * θ - μ ^ 2)) = fun θ => θ ^ 2 := by
        funext θ; ring
      rw [this]; exact hi2
    have e : (fun θ : ℝ => θ ^ 2) = fun θ => (θ - μ) ^ 2 + (2 * μ * θ - μ ^ 2) := by
      funext θ; ring
    have hA : Integrable (fun θ : ℝ => (θ - μ) ^ 2) (gaussianReal μ v) :=
      ((memLp_id_gaussianReal (μ := μ) (v := v) 2).sub (memLp_const μ)).integrable_sq
    have hB : Integrable (fun θ : ℝ => 2 * μ * θ) (gaussianReal μ v) := hi1.const_mul _
    have hC : Integrable (fun θ : ℝ => 2 * μ * θ - μ ^ 2) (gaussianReal μ v) :=
      hB.sub (integrable_const _)
    rw [e, integral_add hA hC, integral_sub hB (integrable_const _),
      integral_const_mul, hvar, integral_id_gaussianReal]
    simp; ring
  have hA : Integrable (fun θ : ℝ => c0 + c1 * θ) (gaussianReal μ v) :=
    (integrable_const c0).add (hi1.const_mul c1)
  have hB : Integrable (fun θ : ℝ => c1 * θ) (gaussianReal μ v) := hi1.const_mul c1
  rw [integral_add hA (hi2.const_mul c2), integral_add (integrable_const _) hB,
    integral_const_mul, integral_const_mul, hsq, integral_id_gaussianReal]
  simp

lemma herd14_pred (P : Params) (hP : Standing P) (x y : ℝ) :
    predictive P x y = gaussianReal (thetaHat P x y) (predVar P).toNNReal := by
  have h3 := eq_3_posterior P hP x y
  obtain ⟨_, hx, hy, _, _⟩ := hP
  unfold predictive
  rw [h3, gaussianReal_conv_gaussianReal, add_zero, predVar,
    Real.toNNReal_add (by unfold postVar; positivity) (by positivity)]

theorem solution (P : Params) (hP : Standing P) :
    Admissible P (closedForm P) ∧
      ∀ (k : Fin P.K) (x y : ℝ),
        closedForm P k x y = (brMean P (closedForm P) k x y, brVar P (closedForm P) k x y) := by
  have hpred := herd14_pred P hP
  obtain ⟨hK, hx, hy, hr0, hr1⟩ := hP
  have hD1 : 0 < (P.τx + P.τy) ^ 2 - P.r * P.τx ^ 2 := by
    have : P.r * P.τx ^ 2 < P.τx ^ 2 := by
      have := pow_pos hx 2; nlinarith
    nlinarith [mul_pos hx hy, pow_pos hy 2]
  have hD2 : 0 < (1 - P.r) * P.τx + P.τy := by
    have : 0 < 1 - P.r := by linarith
    positivity
  have ha : 0 ≤ aCoef P := by
    unfold aCoef
    have : 0 ≤ 1 - P.r := by linarith
    positivity
  have hd : 0 < dCoef P := by
    unfold dCoef
    positivity
  have hW : 0 ≤ predVar P := by unfold predVar postVar; positivity
  have hWr : ((predVar P).toNNReal : ℝ) = predVar P := Real.coe_toNNReal _ hW
  -- generic integrability of polynomials under the predictive law
  have hpoly : ∀ (x y c0 c1 c2 : ℝ),
      Integrable (fun x' : ℝ => c0 + c1 * x' + c2 * x' ^ 2) (predictive P x y) := by
    intro x y c0 c1 c2; rw [hpred]; exact herd14_int _ _ _ _ _
  have hprob : ∀ x y, IsProbabilityMeasure (predictive P x y) := by
    intro x y; rw [hpred]; infer_instance
  refine ⟨?_, ?_⟩
  · intro j
    refine ⟨?_, ?_, ?_⟩
    · apply Continuous.measurable
      unfold closedForm muMS
      fun_prop
    · intro x y
      unfold closedForm
      simp only
      positivity
    · intro x y
      have := hprob x y
      have e1 : (fun x' => (closedForm P j x' y).1) = fun x' =>
          (P.τy / ((1 - P.r) * P.τx + P.τy) * y) + ((1 - P.r) * P.τx / ((1 - P.r) * P.τx + P.τy)) * x'
            + 0 * x' ^ 2 := by
        funext x'; simp only [closedForm, muMS]; ring
      have e2 : (fun x' => (closedForm P j x' y).1 ^ 2) = fun x' =>
          (P.τy / ((1 - P.r) * P.τx + P.τy) * y) ^ 2 +
            (2 * (P.τy / ((1 - P.r) * P.τx + P.τy) * y) *
              ((1 - P.r) * P.τx / ((1 - P.r) * P.τx + P.τy))) * x'
            + ((1 - P.r) * P.τx / ((1 - P.r) * P.τx + P.τy)) ^ 2 * x' ^ 2 := by
        funext x'; simp only [closedForm, muMS]; ring
      have e3 : (fun x' => (closedForm P j x' y).2) = fun x' =>
          (aCoef P * y ^ 2 + dCoef P) + (-2 * aCoef P * y) * x' + aCoef P * x' ^ 2 := by
        funext x'; simp only [closedForm]; ring
      have i3 : Integrable (fun x' => (closedForm P j x' y).2) (predictive P x y) := by
        rw [e3]; exact hpoly _ _ _ _ _
      refine ⟨by rw [e1]; exact hpoly _ _ _ _ _, by rw [e2]; exact hpoly _ _ _ _ _, i3, ?_⟩
      have i4 : Integrable (fun x' => (closedForm P j x' y).2 + |Real.log (dCoef P)|)
          (predictive P x y) := i3.add (integrable_const _)
      refine i4.mono' ?_ ?_
      · apply Continuous.aestronglyMeasurable
        unfold closedForm
        simp only
        apply Continuous.log (by fun_prop)
        intro x'; have : 0 ≤ (x' - y) ^ 2 := sq_nonneg _; positivity
      · refine Filter.Eventually.of_forall (fun x' => ?_)
        simp only [closedForm, Real.norm_eq_abs]
        set z := aCoef P * (x' - y) ^ 2 + dCoef P with hz
        have hdz : dCoef P ≤ z := by
          have : 0 ≤ aCoef P * (x' - y) ^ 2 := by positivity
          linarith
        have hzpos : 0 < z := lt_of_lt_of_le hd hdz
        rw [abs_le]
        constructor
        · have := Real.log_le_log hd hdz
          have := neg_abs_le (Real.log (dCoef P))
          linarith
        · have := Real.log_le_sub_one_of_pos hzpos
          have := abs_nonneg (Real.log (dCoef P))
          linarith
  · intro k x y
    have := hprob x y
    have hn : (0 : ℝ) < (P.K : ℝ) - 1 := by
      have : (2 : ℝ) ≤ P.K := by exact_mod_cast hK
      linarith
    have hcard : ((Finset.univ.erase k).card : ℝ) = (P.K : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by omega)]
      simp
    set A := (1 - P.r) * P.τx / ((1 - P.r) * P.τx + P.τy) with hA
    set B := P.τy / ((1 - P.r) * P.τx + P.τy) with hB
    have hI1 : ∀ j, ∫ x', (closedForm P j x' y).1 ∂predictive P x y
        = B * y + A * thetaHat P x y + 0 * (thetaHat P x y ^ 2 + predVar P) := by
      intro j
      have e1 : (fun x' => (closedForm P j x' y).1) = fun x' => B * y + A * x' + 0 * x' ^ 2 := by
        funext x'; simp only [closedForm, muMS]; ring
      rw [e1, hpred, herd14_poly, hWr]
    have hmean : brMean P (closedForm P) k x y = muMS P x y := by
      unfold brMean
      rw [Finset.sum_congr rfl (fun j _ => hI1 j), Finset.sum_const, nsmul_eq_mul, hcard]
      unfold muMS thetaHat
      rw [hA, hB]
      have hn' : (P.K : ℝ) - 1 ≠ 0 := hn.ne'
      have h1 : P.τy + P.τx ≠ 0 := by positivity
      have h2 : (1 - P.r) * P.τx + P.τy ≠ 0 := hD2.ne'
      field_simp
      ring
    refine Prod.ext ?_ ?_
    · simp only [closedForm]; exact hmean.symm
    · show aCoef P * (x - y) ^ 2 + dCoef P = brVar P (closedForm P) k x y
      unfold brVar
      rw [hmean]
      set u := muMS P x y - B * y with hu
      have hI2 : ∀ j, ∫ x', ((muMS P x y - (closedForm P j x' y).1) ^ 2 + (closedForm P j x' y).2)
          ∂predictive P x y
          = (u ^ 2 + aCoef P * y ^ 2 + dCoef P) + (-2 * u * A - 2 * aCoef P * y) * thetaHat P x y
            + (A ^ 2 + aCoef P) * (thetaHat P x y ^ 2 + predVar P) := by
        intro j
        have e1 : (fun x' => (muMS P x y - (closedForm P j x' y).1) ^ 2 + (closedForm P j x' y).2)
            = fun x' => (u ^ 2 + aCoef P * y ^ 2 + dCoef P) + (-2 * u * A - 2 * aCoef P * y) * x'
              + (A ^ 2 + aCoef P) * x' ^ 2 := by
          funext x'; simp only [closedForm]; rw [hu]; simp only [muMS]; rw [← hA, ← hB]; ring
        rw [e1, hpred, herd14_poly, hWr]
      rw [Finset.sum_congr rfl (fun j _ => hI2 j), Finset.sum_const, nsmul_eq_mul, hcard, hu]
      unfold muMS thetaHat predVar postVar aCoef dCoef
      rw [hA, hB]
      have hn' : (P.K : ℝ) - 1 ≠ 0 := hn.ne'
      have h1 : P.τy + P.τx ≠ 0 := by positivity
      have h2 : (1 - P.r) * P.τx + P.τy ≠ 0 := hD2.ne'
      have h3 : (P.τx + P.τy) ^ 2 - P.r * P.τx ^ 2 ≠ 0 := hD1.ne'
      have h4 : P.τx ≠ 0 := hx.ne'
      field_simp
      ring
