-- Prove2me | solution 1 for HerdingForecast.Equilibrium.ec_11_12_best_response
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:29:23.516788+00:00
-- url     : https://prove2.me/submissions/471f4535-874b-457f-8e19-3c3f451766bf

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model
import Theorems.Thm_HerdingForecast_Equilibrium_eq_3_posterior

open HerdingForecast.Equilibrium MeasureTheory ProbabilityTheory

lemma herd_sq_gauss (μ m : ℝ) (v : NNReal) :
    ∫ θ, (m - θ) ^ 2 ∂gaussianReal μ v = (m - μ) ^ 2 + v := by
  have hi1 : Integrable (fun θ : ℝ => θ) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable le_rfl
  have hi2 : Integrable (fun θ : ℝ => (θ - μ) ^ 2) (gaussianReal μ v) :=
    ((memLp_id_gaussianReal (μ := μ) (v := v) 2).sub (memLp_const μ)).integrable_sq
  have hvar : ∫ θ, (θ - μ) ^ 2 ∂gaussianReal μ v = v := by
    have := variance_fun_id_gaussianReal (μ := μ) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable] at this
    simpa only [integral_id_gaussianReal] using this
  have hlin : ∫ θ, (θ - μ) ∂gaussianReal μ v = 0 := by
    rw [integral_sub hi1 (integrable_const _), integral_id_gaussianReal]; simp
  have hrw : (fun θ : ℝ => (m - θ) ^ 2) =
      fun θ => (θ - μ) ^ 2 + ((-2 * (m - μ)) * (θ - μ) + (m - μ) ^ 2) := by
    funext θ; ring
  have hi3 : Integrable (fun θ : ℝ => (-2 * (m - μ)) * (θ - μ)) (gaussianReal μ v) :=
    (hi1.sub (integrable_const μ)).const_mul _
  have hi4 : Integrable (fun θ : ℝ => (-2 * (m - μ)) * (θ - μ) + (m - μ) ^ 2) (gaussianReal μ v) :=
    hi3.add (integrable_const _)
  rw [hrw, integral_add hi2 hi4, integral_add hi3 (integrable_const _),
    integral_const_mul, hlin, hvar]
  simp; ring

theorem solution (P : Params) (hP : Standing P) (s : Profile P.K)
    (hs : Admissible P s) (k : Fin P.K) (x y : ℝ) :
    0 < brVar P s k x y ∧
      ∀ a : ℝ × ℝ, 0 < a.2 → a ≠ (brMean P s k x y, brVar P s k x y) →
        objective P s k x y (brMean P s k x y, brVar P s k x y) < objective P s k x y a := by
  have hpost : posterior P x y = gaussianReal (thetaHat P x y) (postVar P).toNNReal :=
    eq_3_posterior P hP x y
  obtain ⟨hK, hx, hy, hr0, hr1⟩ := hP
  have hVpos : 0 < postVar P := by unfold postVar; positivity
  have hVr : ((postVar P).toNNReal : ℝ) = postVar P := Real.coe_toNNReal _ hVpos.le
  have : IsProbabilityMeasure (predictive P x y) := by
    unfold predictive; rw [hpost]; infer_instance
  have hn : (0 : ℝ) < (P.K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P.K := by exact_mod_cast hK
    linarith
  have hcard : ((Finset.univ.erase k).card : ℝ) = (P.K : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp
  obtain ⟨M, hM⟩ : ∃ M : Fin P.K → ℝ, ∀ j, ∫ x', (s j x' y).1 ∂predictive P x y = M j :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Fin P.K → ℝ,
      ∀ j, ∫ x', ((s j x' y).1 ^ 2 + (s j x' y).2) ∂predictive P x y = T j :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin P.K → ℝ,
      ∀ j, ∫ x', Real.log (s j x' y).2 ∂predictive P x y = L j :=
    ⟨_, fun _ => rfl⟩
  -- per-opponent quadratic term
  have hG : ∀ (m : ℝ) j, ∫ x', ((m - (s j x' y).1) ^ 2 + (s j x' y).2) ∂predictive P x y
      = m ^ 2 - 2 * m * M j + T j := by
    intro m j
    obtain ⟨_, _, hint⟩ := hs j
    obtain ⟨h1, h2, h3, _⟩ := hint x y
    have hrw : (fun x' => (m - (s j x' y).1) ^ 2 + (s j x' y).2) =
        fun x' => m ^ 2 + ((-2 * m) * (s j x' y).1 + ((s j x' y).1 ^ 2 + (s j x' y).2)) := by
      funext x'; ring
    have i1 : Integrable (fun x' => (-2 * m) * (s j x' y).1) (predictive P x y) := h1.const_mul _
    have i2 : Integrable (fun x' => (s j x' y).1 ^ 2 + (s j x' y).2) (predictive P x y) := h2.add h3
    have i3 : Integrable (fun x' => (-2 * m) * (s j x' y).1 + ((s j x' y).1 ^ 2 + (s j x' y).2))
      (predictive P x y) := i1.add i2
    rw [hrw, integral_add (integrable_const _) i3, integral_add i1 i2, integral_const_mul, hM, hT]
    simp; ring
  -- per-opponent KL term
  have hKL : ∀ (m v : ℝ), 0 < v → ∀ j, ∫ x', dKL (s j x' y) (m, v) ∂predictive P x y
      = ((m ^ 2 - 2 * m * M j + T j) / v - 1 + Real.log v - L j) / 2 := by
    intro m v hv j
    obtain ⟨_, _, hint⟩ := hs j
    obtain ⟨h1, h2, h3, h4⟩ := hint x y
    have hq : Integrable (fun x' => (m - (s j x' y).1) ^ 2 + (s j x' y).2) (predictive P x y) := by
      have hrw : (fun x' => (m - (s j x' y).1) ^ 2 + (s j x' y).2) =
          fun x' => m ^ 2 + ((-2 * m) * (s j x' y).1 + ((s j x' y).1 ^ 2 + (s j x' y).2)) := by
        funext x'; ring
      rw [hrw]; exact (integrable_const _).add ((h1.const_mul _).add (h2.add h3))
    have hrw : (fun x' => dKL (s j x' y) (m, v)) = fun x' =>
        (1 / (2 * v)) * ((m - (s j x' y).1) ^ 2 + (s j x' y).2) +
          ((-1 + Real.log v) / 2 + (-1 / 2) * Real.log (s j x' y).2) := by
      funext x'; unfold dKL; simp only; field_simp; ring
    have i1 : Integrable (fun x' => (1 / (2 * v)) * ((m - (s j x' y).1) ^ 2 + (s j x' y).2))
      (predictive P x y) := hq.const_mul _
    have i2 : Integrable (fun x' => (-1 / 2) * Real.log (s j x' y).2) (predictive P x y) :=
      h4.const_mul _
    have i3 : Integrable (fun x' => (-1 + Real.log v) / 2 + (-1 / 2) * Real.log (s j x' y).2)
      (predictive P x y) := (integrable_const _).add i2
    rw [hrw, integral_add i1 i3, integral_add (integrable_const _) i2, integral_const_mul,
      integral_const_mul,
      hG, hL]
    simp; field_simp; ring
  -- log-score term
  have hLS : ∀ (m v : ℝ), 0 < v → ∫ θ, logScore (m, v) θ ∂posterior P x y
      = ((m - thetaHat P x y) ^ 2 + postVar P) / (2 * v) + Real.log v / 2
        + Real.log (2 * Real.pi) / 2 := by
    intro m v hv
    rw [hpost]
    have hi : Integrable (fun θ : ℝ => (m - θ) ^ 2)
        (gaussianReal (thetaHat P x y) (postVar P).toNNReal) := by
      have := ((memLp_const m).sub (memLp_id_gaussianReal (μ := thetaHat P x y)
        (v := (postVar P).toNNReal) 2)).integrable_sq
      simpa using this
    have hrw : (fun θ => logScore (m, v) θ) = fun θ =>
        (1 / (2 * v)) * (m - θ) ^ 2 + (Real.log v / 2 + Real.log (2 * Real.pi) / 2) := by
      funext θ; unfold logScore; simp only; field_simp; ring
    have i1 : Integrable (fun θ : ℝ => (1 / (2 * v)) * (m - θ) ^ 2)
        (gaussianReal (thetaHat P x y) (postVar P).toNNReal) := hi.const_mul _
    rw [hrw, integral_add i1 (integrable_const _), integral_const_mul,
      herd_sq_gauss, hVr]
    simp; field_simp; ring
  -- sums
  set n : ℝ := (P.K : ℝ) - 1 with hn_def
  set SM := ∑ j ∈ Finset.univ.erase k, M j with hSM
  set ST := ∑ j ∈ Finset.univ.erase k, T j with hST
  set SL := ∑ j ∈ Finset.univ.erase k, L j with hSL
  set th := thetaHat P x y with hth
  set V := postVar P with hV
  set r := P.r with hr
  have hsumG : ∀ m : ℝ, ∑ j ∈ Finset.univ.erase k, (m ^ 2 - 2 * m * M j + T j)
      = n * m ^ 2 - 2 * m * SM + ST := by
    intro m
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard,
      ← Finset.mul_sum]
  have hsumK : ∀ m v : ℝ, ∑ j ∈ Finset.univ.erase k,
      ((m ^ 2 - 2 * m * M j + T j) / v - 1 + Real.log v - L j) / 2
      = ((n * m ^ 2 - 2 * m * SM + ST) / v - n + n * Real.log v - SL) / 2 := by
    intro m v
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_div, hsumG, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      hcard]
    ring
  set μs := brMean P s k x y with hμs
  have hμs' : μs = (1 - r) * th + r * (1 / n) * SM := by
    rw [hμs, brMean]
    simp only [hM]
    rw [← hn_def, ← hr, ← hth, ← hSM]
  set vs := brVar P s k x y with hvs
  have hvs' : vs = (1 - r) * ((μs - th) ^ 2 + V) + r * (1 / n) * (n * μs ^ 2 - 2 * μs * SM + ST) := by
    rw [hvs, brVar, ← hμs]
    simp only [hG]
    rw [hsumG]
  have hvpos : 0 < vs := by
    have h0 : 0 ≤ ∑ j ∈ Finset.univ.erase k,
        ∫ x', ((μs - (s j x' y).1) ^ 2 + (s j x' y).2) ∂predictive P x y := by
      apply Finset.sum_nonneg
      intro j _
      apply integral_nonneg
      intro x'
      have := ((hs j).2.1 x' y).le
      positivity
    have hvsI : vs = (1 - r) * ((μs - th) ^ 2 + V) + r * (1 / n) * ∑ j ∈ Finset.univ.erase k,
        ∫ x', ((μs - (s j x' y).1) ^ 2 + (s j x' y).2) ∂predictive P x y := by
      rw [hvs, brVar, ← hμs]
    rw [hvsI]
    have h1 : 0 < 1 - r := by linarith
    have h2 : 0 ≤ r * (1 / n) := by positivity
    have h3 : 0 < (1 - r) * ((μs - th) ^ 2 + V) := by positivity
    nlinarith [mul_nonneg h2 h0]
  -- objective in closed form
  set c0 : ℝ := (1 - r) * (Real.log (2 * Real.pi) / 2) + r * (1 / n) * ((- n - SL) / 2) with hc0
  set Q : ℝ → ℝ := fun m => (1 - r) * ((m - th) ^ 2 + V) + r * (1 / n) * (n * m ^ 2 - 2 * m * SM + ST)
    with hQ
  have hobj : ∀ m v : ℝ, 0 < v → objective P s k x y (m, v) = Q m / (2 * v) + Real.log v / 2 + c0 := by
    intro m v hv
    unfold objective
    rw [hLS m v hv, Finset.sum_congr rfl (fun j _ => hKL m v hv j), hsumK, ← hn_def, ← hr]
    simp only [hQ, hc0]
    have hn' : n ≠ 0 := hn.ne'
    field_simp
    ring
  have hQm : ∀ m, Q m = vs + (m - μs) ^ 2 := by
    intro m
    simp only [hQ]
    rw [hvs', hμs']
    have hn' : n ≠ 0 := hn.ne'
    field_simp
    ring
  refine ⟨hvpos, ?_⟩
  rintro ⟨m, v⟩ hv hne
  simp only at hv
  rw [hobj _ _ hvpos, hobj _ _ hv, hQm, hQm]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  have hlog : Real.log vs - Real.log v ≤ vs / v - 1 := by
    rw [← Real.log_div hvpos.ne' hv.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have key : vs / (2 * vs) = 1 / 2 := by field_simp
  rw [key]
  by_cases hm : m = μs
  · subst hm
    have hvne : v ≠ vs := fun h => hne (by rw [h])
    have hlt : Real.log vs - Real.log v < vs / v - 1 := by
      rw [← Real.log_div hvpos.ne' hv.ne']
      apply Real.log_lt_sub_one_of_pos (by positivity)
      intro h; apply hvne; field_simp at h; linarith
    have : (vs + (μs - μs) ^ 2) / (2 * v) = (vs / v) / 2 := by
      rw [sub_self]; field_simp; ring
    rw [this]; linarith
  · have hpos : 0 < (m - μs) ^ 2 := by
      have : m - μs ≠ 0 := sub_ne_zero.mpr hm
      positivity
    have : (vs + (m - μs) ^ 2) / (2 * v) = (vs / v) / 2 + (m - μs) ^ 2 / (2 * v) := by
      field_simp
    have h2 : 0 < (m - μs) ^ 2 / (2 * v) := by positivity
    rw [this]; linarith
