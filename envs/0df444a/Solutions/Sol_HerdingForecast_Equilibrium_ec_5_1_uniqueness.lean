-- Prove2me | solution 1 for HerdingForecast.Equilibrium.ec_5_1_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:47:29.780253+00:00
-- url     : https://prove2.me/submissions/9a87c595-5741-4c51-9170-fa2c242a3f85

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model
import Theorems.Thm_HerdingForecast_Equilibrium_eq_3_posterior
import Theorems.Thm_HerdingForecast_Equilibrium_ec_14_closed_form_solves

open HerdingForecast.Equilibrium MeasureTheory ProbabilityTheory

/-- Geometric contraction: if `F ≤ ρ T F`, `ρ T G ≤ σ G`, `ρ T q ≤ τ q` and `F ≤ c G + c' q`
with `σ, τ < 1`, then `F ≤ 0`. -/
lemma herd51_iter (T : ℝ → Measure ℝ) (F G q : ℝ → ℝ) (ρ σ τ c c' : ℝ) (hρ : 0 ≤ ρ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hFi : ∀ x, Integrable F (T x)) (hGi : ∀ x, Integrable G (T x))
    (hqi : ∀ x, Integrable q (T x))
    (hF : ∀ x, F x ≤ ρ * ∫ z, F z ∂T x) (hG : ∀ x, ρ * ∫ z, G z ∂T x ≤ σ * G x)
    (hq : ∀ x, ρ * ∫ z, q z ∂T x ≤ τ * q x)
    (hb : ∀ x, F x ≤ c * G x + c' * q x) : ∀ x, F x ≤ 0 := by
  have key : ∀ n : ℕ, ∀ x, F x ≤ c * σ ^ n * G x + c' * τ ^ n * q x := by
    intro n
    induction n with
    | zero => intro x; simpa using hb x
    | succ n ih =>
      intro x
      have hint : Integrable (fun z => c * σ ^ n * G z + c' * τ ^ n * q z) (T x) :=
        ((hGi x).const_mul _).add ((hqi x).const_mul _)
      have h1 : ∫ z, F z ∂T x ≤ ∫ z, (c * σ ^ n * G z + c' * τ ^ n * q z) ∂T x :=
        integral_mono (hFi x) hint ih
      rw [integral_add ((hGi x).const_mul _) ((hqi x).const_mul _), integral_const_mul,
        integral_const_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hρ
      have hA : 0 ≤ c * σ ^ n := mul_nonneg hc (pow_nonneg hσ0 n)
      have hB : 0 ≤ c' * τ ^ n := mul_nonneg hc' (pow_nonneg hτ0 n)
      have h3 := mul_le_mul_of_nonneg_left (hG x) hA
      have h4 := mul_le_mul_of_nonneg_left (hq x) hB
      calc F x ≤ ρ * ∫ z, F z ∂T x := hF x
        _ ≤ ρ * (c * σ ^ n * ∫ z, G z ∂T x + c' * τ ^ n * ∫ z, q z ∂T x) := h2
        _ = c * σ ^ n * (ρ * ∫ z, G z ∂T x) + c' * τ ^ n * (ρ * ∫ z, q z ∂T x) := by ring
        _ ≤ c * σ ^ n * (σ * G x) + c' * τ ^ n * (τ * q x) := add_le_add h3 h4
        _ = c * σ ^ (n + 1) * G x + c' * τ ^ (n + 1) * q x := by ring
  intro x
  have ht : Filter.Tendsto (fun n : ℕ => c * σ ^ n * G x + c' * τ ^ n * q x) Filter.atTop
      (nhds (c * 0 * G x + c' * 0 * q x)) := by
    apply Filter.Tendsto.add
    · exact ((tendsto_pow_atTop_nhds_zero_of_lt_one hσ0 hσ1).const_mul c).mul_const _
    · exact ((tendsto_pow_atTop_nhds_zero_of_lt_one hτ0 hτ1).const_mul c').mul_const _
  simp only [mul_zero, zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht (fun n => key n x)

/-- Double sum over ordered pairs of distinct indices. -/
lemma herd51_swap {K : ℕ} (a : Fin K → ℝ) :
    ∑ k : Fin K, ∑ j ∈ Finset.univ.erase k, a j = ((K : ℝ) - 1) * ∑ j, a j := by
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Jensen for the square on a probability measure. -/
lemma herd51_sq_int {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun z => f z ^ 2) μ) :
    (∫ z, f z ∂μ) ^ 2 ≤ ∫ z, f z ^ 2 ∂μ := by
  set m := ∫ z, f z ∂μ
  have h0 : 0 ≤ ∫ z, (f z - m) ^ 2 ∂μ := integral_nonneg (fun z => sq_nonneg _)
  have e : (fun z => (f z - m) ^ 2) = fun z => f z ^ 2 + ((-2 * m) * f z + m ^ 2) := by
    funext z; ring
  have i1 : Integrable (fun z => (-2 * m) * f z) μ := hf.const_mul _
  have i2 : Integrable (fun z => (-2 * m) * f z + m ^ 2) μ := i1.add (integrable_const _)
  rw [e, integral_add hf2 i2, integral_add i1 (integrable_const _), integral_const_mul] at h0
  simp at h0
  nlinarith

lemma herd51_int (μ c0 c1 c2 : ℝ) (v : NNReal) :
    Integrable (fun θ : ℝ => c0 + c1 * θ + c2 * θ ^ 2) (gaussianReal μ v) := by
  have hi1 : Integrable (fun θ : ℝ => θ) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable le_rfl
  have hi2 : Integrable (fun θ : ℝ => θ ^ 2) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 2).integrable_sq
  exact ((integrable_const c0).add (hi1.const_mul c1)).add (hi2.const_mul c2)

lemma herd51_poly (μ c0 c1 c2 : ℝ) (v : NNReal) :
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

lemma herd51_exp (μ β : ℝ) (v : NNReal) :
    ∫ θ, Real.exp (β * θ) ∂gaussianReal μ v = Real.exp (μ * β + v * β ^ 2 / 2) := by
  have := congrFun (mgf_fun_id_gaussianReal (μ := μ) (v := v)) β
  simpa [mgf] using this

lemma herd51_cosh (μ β y : ℝ) (v : NNReal) :
    Integrable (fun θ => Real.cosh (β * (θ - y))) (gaussianReal μ v) ∧
    ∫ θ, Real.cosh (β * (θ - y)) ∂gaussianReal μ v
      = Real.exp (v * β ^ 2 / 2) * Real.cosh (β * (μ - y)) := by
  have e : (fun θ => Real.cosh (β * (θ - y))) = fun θ =>
      (Real.exp (-(β * y)) / 2) * Real.exp (β * θ) + (Real.exp (β * y) / 2) * Real.exp ((-β) * θ) := by
    funext θ
    rw [Real.cosh_eq]
    have h1 : Real.exp (β * (θ - y)) = Real.exp (-(β * y)) * Real.exp (β * θ) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(β * (θ - y))) = Real.exp (β * y) * Real.exp ((-β) * θ) := by
      rw [← Real.exp_add]; ring_nf
    rw [h1, h2]; ring
  have i1 : Integrable (fun θ => (Real.exp (-(β * y)) / 2) * Real.exp (β * θ)) (gaussianReal μ v) :=
    (integrable_exp_mul_gaussianReal β).const_mul _
  have i2 : Integrable (fun θ => (Real.exp (β * y) / 2) * Real.exp ((-β) * θ)) (gaussianReal μ v) :=
    (integrable_exp_mul_gaussianReal (-β)).const_mul _
  refine ⟨by rw [e]; exact i1.add i2, ?_⟩
  rw [e, integral_add i1 i2, integral_const_mul, integral_const_mul, herd51_exp, herd51_exp,
    Real.cosh_eq]
  have h1 : Real.exp (-(β * y)) * Real.exp (μ * β + v * β ^ 2 / 2)
      = Real.exp (v * β ^ 2 / 2) * Real.exp (β * (μ - y)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h2 : Real.exp (β * y) * Real.exp (μ * (-β) + v * (-β) ^ 2 / 2)
      = Real.exp (v * β ^ 2 / 2) * Real.exp (-(β * (μ - y))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  linear_combination h1 / 2 + h2 / 2

lemma herd51_growth (β y : ℝ) (hβ : 0 < β) (N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, (1 + |y| + |x - y|) ^ N ≤ c * Real.cosh (β * (x - y)) := by
  refine ⟨2 * N.factorial * Real.exp (β * (1 + |y|)) / β ^ N, by positivity, fun x => ?_⟩
  set w := 1 + |y| + |x - y| with hw
  have hw0 : 0 ≤ w := by positivity
  have h1 := Real.pow_div_factorial_le_exp (x := β * w) (mul_nonneg hβ.le hw0) N
  have h2 : Real.exp (β * w) = Real.exp (β * (1 + |y|)) * Real.exp (|β * (x - y)|) := by
    rw [← Real.exp_add, abs_mul, abs_of_pos hβ, hw]; ring_nf
  have h3 : Real.exp (|β * (x - y)|) ≤ 2 * Real.cosh (β * (x - y)) := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have := Real.exp_pos (-|β * (x - y)|)
    linarith
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hbN : 0 < β ^ N := pow_pos hβ N
  rw [mul_pow, div_le_iff₀ hf] at h1
  have : w ^ N * β ^ N ≤ N.factorial * (Real.exp (β * (1 + |y|)) * (2 * Real.cosh (β * (x - y)))) := by
    calc w ^ N * β ^ N = β ^ N * w ^ N := by ring
      _ ≤ Real.exp (β * w) * N.factorial := h1
      _ = N.factorial * (Real.exp (β * (1 + |y|)) * Real.exp (|β * (x - y)|)) := by rw [h2]; ring
      _ ≤ _ := by gcongr
  calc w ^ N = (w ^ N * β ^ N) / β ^ N := by field_simp
    _ ≤ (N.factorial * (Real.exp (β * (1 + |y|)) * (2 * Real.cosh (β * (x - y))))) / β ^ N := by
        gcongr
    _ = _ := by ring

lemma herd51_aux0 (a b : ℝ) : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

lemma herd51_aux1 (D t κ g c M : ℝ) (_hc : 0 < c) (h3 : D ^ 2 ≤ g / c) (hM : 0 ≤ M) :
    (D - κ * t) ^ 2 ≤ 2 * (g / c) + 2 * κ ^ 2 * (t ^ 2 + M) := by
  nlinarith [sq_nonneg (D + κ * t), sq_nonneg κ, mul_nonneg (sq_nonneg κ) hM]

lemma herd51_aux2 (α t W M l : ℝ) (hα : α ^ 2 ≤ l) (hWM : W + M = l * M) :
    α ^ 2 * t ^ 2 + W + M ≤ l * (t ^ 2 + M) := by
  nlinarith [mul_le_mul_of_nonneg_right hα (sq_nonneg t)]

lemma herd51_aux3 (x y : ℝ) (N : ℕ) : 1 + |x| ^ N ≤ 2 * (1 + |y| + |x - y|) ^ N := by
  have hw : 1 ≤ 1 + |y| + |x - y| := by have := abs_nonneg y; have := abs_nonneg (x - y); linarith
  have hx : |x| ≤ 1 + |y| + |x - y| := by
    have := abs_sub_abs_le_abs_sub x y; linarith
  have h1 : 1 ≤ (1 + |y| + |x - y|) ^ N := one_le_pow₀ hw
  have h2 : |x| ^ N ≤ (1 + |y| + |x - y|) ^ N := pow_le_pow_left₀ (abs_nonneg x) hx N
  linarith

lemma herd51_aux4 (x y : ℝ) : (x - y) ^ 2 ≤ (1 + |y| + |x - y|) ^ 2 := by
  have h : |x - y| ≤ 1 + |y| + |x - y| := by have := abs_nonneg y; linarith
  have := pow_le_pow_left₀ (abs_nonneg (x - y)) h 2
  rwa [sq_abs] at this

set_option maxHeartbeats 2000000 in
theorem solution (P : Params) (hP : Standing P) (s : Profile P.K)
    (hs : Admissible P s)
    (hfoc : ∀ (k : Fin P.K) (x y : ℝ), s k x y = (brMean P s k x y, brVar P s k x y)) :
    (∀ (k : Fin P.K) (x y : ℝ), (s k x y).1 = muMS P x y) ∧
      (PolyGrowth s → s = closedForm P) := by
  have hcf := ec_14_closed_form_solves P hP
  have hpred : ∀ x y, predictive P x y = gaussianReal (thetaHat P x y) (predVar P).toNNReal := by
    intro x y
    have h3 := eq_3_posterior P hP x y
    obtain ⟨_, hx, hy, _, _⟩ := hP
    unfold predictive
    rw [h3, gaussianReal_conv_gaussianReal, add_zero, predVar,
      Real.toNNReal_add (by unfold postVar; positivity) (by positivity)]
  obtain ⟨hK, hx, hy, hr0, hr1⟩ := hP
  have hprob : ∀ x y, IsProbabilityMeasure (predictive P x y) := by
    intro x y; rw [hpred]; infer_instance
  have hn : (0 : ℝ) < (P.K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P.K := by exact_mod_cast hK
    linarith
  have hn' : (P.K : ℝ) - 1 ≠ 0 := hn.ne'
  have hcard : ∀ k : Fin P.K, ((Finset.univ.erase k).card : ℝ) = (P.K : ℝ) - 1 := by
    intro k
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp
  have hVpos : 0 < postVar P := by unfold postVar; positivity
  have hWpos : 0 < predVar P := by unfold predVar postVar; positivity
  have hWr : ((predVar P).toNNReal : ℝ) = predVar P := Real.coe_toNNReal _ hWpos.le
  have hD2 : 0 < (1 - P.r) * P.τx + P.τy := by
    have : 0 < 1 - P.r := by linarith
    positivity
  set r := P.r with hr
  set n : ℝ := (P.K : ℝ) - 1 with hn_def
  -- polynomial integrability and integrals under the predictive law
  have hpolyI : ∀ (x y c0 c1 c2 : ℝ),
      Integrable (fun x' : ℝ => c0 + c1 * x' + c2 * x' ^ 2) (predictive P x y) := by
    intro x y c0 c1 c2; rw [hpred]; exact herd51_int _ _ _ _ _
  have hpolyE : ∀ (x y c0 c1 c2 : ℝ), ∫ x', (c0 + c1 * x' + c2 * x' ^ 2) ∂predictive P x y
      = c0 + c1 * thetaHat P x y + c2 * (thetaHat P x y ^ 2 + predVar P) := by
    intro x y c0 c1 c2; rw [hpred, herd51_poly, hWr]
  set A := (1 - r) * P.τx / ((1 - r) * P.τx + P.τy) with hA
  set B := P.τy / ((1 - r) * P.τx + P.τy) with hB
  have hms : ∀ x y, muMS P x y = B * y + A * x + 0 * x ^ 2 := by
    intro x y; unfold muMS; rw [← hr, ← hA, ← hB]; ring
  have hMSi : ∀ x y, Integrable (fun x' => muMS P x' y) (predictive P x y) := by
    intro x y; simp_rw [hms]; exact hpolyI _ _ _ _ _
  have hMS2i : ∀ x y, Integrable (fun x' => muMS P x' y ^ 2) (predictive P x y) := by
    intro x y
    have e : (fun x' => muMS P x' y ^ 2) = fun x' => (B * y) ^ 2 + (2 * B * y * A) * x' + A ^ 2 * x' ^ 2 := by
      funext x'; rw [hms]; ring
    rw [e]; exact hpolyI _ _ _ _ _
  -- the mean and variance of `s` from the FOCs
  have hm1 : ∀ (k : Fin P.K) (x y : ℝ), (s k x y).1 = brMean P s k x y := by
    intro k x y; have := congrArg Prod.fst (hfoc k x y); simpa using this
  have hv1 : ∀ (k : Fin P.K) (x y : ℝ), (s k x y).2 = brVar P s k x y := by
    intro k x y; have := congrArg Prod.snd (hfoc k x y); simpa using this
  -- the closed form's mean equation
  have hmcf : ∀ (k : Fin P.K) (x y : ℝ), muMS P x y = (1 - r) * thetaHat P x y
      + r * (1 / n) * ∑ j ∈ Finset.univ.erase k, ∫ x', muMS P x' y ∂predictive P x y := by
    intro k x y
    have := congrArg Prod.fst (hcf.2 k x y)
    simpa [closedForm, brMean] using this
  have hdiff : ∀ (k : Fin P.K) (x y : ℝ), (s k x y).1 - muMS P x y = r * (1 / n) *
      ∑ j ∈ Finset.univ.erase k, ∫ x', ((s j x' y).1 - muMS P x' y) ∂predictive P x y := by
    intro k x y
    rw [hm1 k x y, hmcf k x y]
    unfold brMean
    rw [← hr, ← hn_def]
    have : ∀ j ∈ Finset.univ.erase k, ∫ x', ((s j x' y).1 - muMS P x' y) ∂predictive P x y
        = ∫ x', (s j x' y).1 ∂predictive P x y - ∫ x', muMS P x' y ∂predictive P x y :=
      fun j _ => integral_sub ((hs j).2.2 x y).1 (hMSi x y)
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    ring
  -- lower bound on the variance from the FOC
  have hvarlb : ∀ (k : Fin P.K) (x y : ℝ), (1 - r) * ((s k x y).1 - thetaHat P x y) ^ 2
      + r * (1 / n) * ∑ j ∈ Finset.univ.erase k, ∫ x', (s j x' y).2 ∂predictive P x y
      ≤ (s k x y).2 := by
    intro k x y
    rw [hv1 k x y]
    unfold brVar
    rw [← hm1 k x y, ← hr, ← hn_def]
    have h1 : (1 - r) * ((s k x y).1 - thetaHat P x y) ^ 2
        ≤ (1 - r) * (((s k x y).1 - thetaHat P x y) ^ 2 + postVar P) := by
      have : 0 ≤ 1 - r := by linarith
      nlinarith
    have h2 : ∑ j ∈ Finset.univ.erase k, ∫ x', (s j x' y).2 ∂predictive P x y
        ≤ ∑ j ∈ Finset.univ.erase k,
          ∫ x', (((s k x y).1 - (s j x' y).1) ^ 2 + (s j x' y).2) ∂predictive P x y := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨i1, i2, i3, _⟩ := (hs j).2.2 x y
      have iq : Integrable (fun x' => ((s k x y).1 - (s j x' y).1) ^ 2 + (s j x' y).2)
          (predictive P x y) := by
        have e : (fun x' => ((s k x y).1 - (s j x' y).1) ^ 2 + (s j x' y).2) = fun x' =>
            (s k x y).1 ^ 2 + ((-2 * (s k x y).1) * (s j x' y).1 + ((s j x' y).1 ^ 2 + (s j x' y).2)) := by
          funext x'; ring
        rw [e]; exact (integrable_const _).add ((i1.const_mul _).add (i2.add i3))
      exact integral_mono i3 iq (fun x' => by simp only; nlinarith [sq_nonneg ((s k x y).1 - (s j x' y).1)])
    have h3 : 0 ≤ r * (1 / n) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hα0 : 0 < P.τx / (P.τy + P.τx) := by positivity
  have hα1 : P.τx / (P.τy + P.τx) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hθ : ∀ x y : ℝ, thetaHat P x y - y = (P.τx / (P.τy + P.τx)) * (x - y) := by
    intro x y; unfold thetaHat
    have : P.τy + P.τx ≠ 0 := by positivity
    field_simp; ring
  set κ := A - P.τx / (P.τy + P.τx) with hκ
  have hmsθ : ∀ x y : ℝ, muMS P x y - thetaHat P x y = κ * (x - y) := by
    intro x y; rw [hms]; unfold thetaHat; rw [hκ, hA, hB]
    have : P.τy + P.τx ≠ 0 := by positivity
    have : (1 - r) * P.τx + P.τy ≠ 0 := hD2.ne'
    field_simp; ring
  have hr1' : 0 < 1 - r := by linarith
  have item1 : ∀ (k : Fin P.K) (x y : ℝ), (s k x y).1 = muMS P x y := by
    intro k₀ x₀ y
    have hr2 : 0 < 1 - r ^ 2 := by nlinarith
    set M : ℝ := predVar P / (1 - r ^ 2) with hM
    have hMpos : 0 < M := by positivity
    set F : ℝ → ℝ := fun x => ∑ j, ((s j x y).1 - muMS P x y) ^ 2 with hFdef
    set G : ℝ → ℝ := fun x => ∑ j, (s j x y).2 with hGdef
    set q : ℝ → ℝ := fun x => (x - y) ^ 2 + M with hqdef
    have hf2i : ∀ (j : Fin P.K) (x : ℝ),
        Integrable (fun x' => ((s j x' y).1 - muMS P x' y) ^ 2) (predictive P x y) := by
      intro j x
      obtain ⟨i1, i2, _, _⟩ := (hs j).2.2 x y
      refine Integrable.mono' ((i2.add (hMS2i x y)).const_mul 2) ?_ ?_
      · exact ((i1.sub (hMSi x y)).aestronglyMeasurable).pow 2
      · refine Filter.Eventually.of_forall (fun x' => ?_)
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (sq_nonneg _)]
        exact herd51_aux0 _ _
    have hFi : ∀ x, Integrable F (predictive P x y) :=
      fun x => integrable_finsetSum _ (fun j _ => hf2i j x)
    have hGi : ∀ x, Integrable G (predictive P x y) :=
      fun x => integrable_finsetSum _ (fun j _ => ((hs j).2.2 x y).2.2.1)
    have hqe : q = fun x' => (y ^ 2 + M) + (-2 * y) * x' + 1 * x' ^ 2 := by
      funext x'; simp only [hqdef]; ring
    have hqi : ∀ x, Integrable q (predictive P x y) := by
      intro x; rw [hqe]; exact hpolyI _ _ _ _ _
    -- F ≤ r² T F
    have hF : ∀ x, F x ≤ r ^ 2 * ∫ z, F z ∂predictive P x y := by
      intro x
      have := hprob x y
      have hjen : ∀ j, (∫ x', ((s j x' y).1 - muMS P x' y) ∂predictive P x y) ^ 2
          ≤ ∫ x', ((s j x' y).1 - muMS P x' y) ^ 2 ∂predictive P x y :=
        fun j => herd51_sq_int (((hs j).2.2 x y).1.sub (hMSi x y)) (hf2i j x)
      have hk : ∀ k : Fin P.K, ((s k x y).1 - muMS P x y) ^ 2 ≤ r ^ 2 * (1 / n) *
          ∑ j ∈ Finset.univ.erase k, ∫ x', ((s j x' y).1 - muMS P x' y) ^ 2 ∂predictive P x y := by
        intro k
        rw [hdiff k x y]
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase k)
          (f := fun j => ∫ x', ((s j x' y).1 - muMS P x' y) ∂predictive P x y)
        rw [hcard k] at hcs
        have hsum := Finset.sum_le_sum (s := Finset.univ.erase k) (fun j _ => hjen j)
        have hr2' : 0 ≤ r ^ 2 * (1 / n) ^ 2 := by positivity
        calc (r * (1 / n) * ∑ j ∈ Finset.univ.erase k,
              ∫ x', ((s j x' y).1 - muMS P x' y) ∂predictive P x y) ^ 2
            = r ^ 2 * (1 / n) ^ 2 * (∑ j ∈ Finset.univ.erase k,
              ∫ x', ((s j x' y).1 - muMS P x' y) ∂predictive P x y) ^ 2 := by ring
          _ ≤ r ^ 2 * (1 / n) ^ 2 * (n * ∑ j ∈ Finset.univ.erase k,
              (∫ x', ((s j x' y).1 - muMS P x' y) ∂predictive P x y) ^ 2) :=
            mul_le_mul_of_nonneg_left hcs hr2'
          _ ≤ r ^ 2 * (1 / n) ^ 2 * (n * ∑ j ∈ Finset.univ.erase k,
              ∫ x', ((s j x' y).1 - muMS P x' y) ^ 2 ∂predictive P x y) := by
            apply mul_le_mul_of_nonneg_left _ hr2'
            exact mul_le_mul_of_nonneg_left hsum hn.le
          _ = _ := by field_simp
      calc F x = ∑ k, ((s k x y).1 - muMS P x y) ^ 2 := rfl
        _ ≤ ∑ k : Fin P.K, r ^ 2 * (1 / n) * ∑ j ∈ Finset.univ.erase k,
              ∫ x', ((s j x' y).1 - muMS P x' y) ^ 2 ∂predictive P x y :=
            Finset.sum_le_sum (fun k _ => hk k)
        _ = r ^ 2 * (1 / n) * (n * ∑ j : Fin P.K,
              ∫ x', ((s j x' y).1 - muMS P x' y) ^ 2 ∂predictive P x y) := by
            rw [← Finset.mul_sum, herd51_swap]
        _ = r ^ 2 * ∫ z, F z ∂predictive P x y := by
            rw [hFdef, integral_finsetSum _ (fun j _ => hf2i j x)]
            field_simp
    -- r T G ≤ G
    have hGT : ∀ x, r * ∫ z, G z ∂predictive P x y ≤ G x := by
      intro x
      have hk : ∀ k : Fin P.K, r * (1 / n) * ∑ j ∈ Finset.univ.erase k,
          ∫ x', (s j x' y).2 ∂predictive P x y ≤ (s k x y).2 := by
        intro k
        have := hvarlb k x y
        have : 0 ≤ (1 - r) * ((s k x y).1 - thetaHat P x y) ^ 2 := by positivity
        linarith
      calc r * ∫ z, G z ∂predictive P x y
          = r * (1 / n) * (n * ∑ j : Fin P.K, ∫ x', (s j x' y).2 ∂predictive P x y) := by
            rw [hGdef, integral_finsetSum _ (fun j _ => ((hs j).2.2 x y).2.2.1)]
            field_simp
        _ = ∑ k : Fin P.K, r * (1 / n) * ∑ j ∈ Finset.univ.erase k,
              ∫ x', (s j x' y).2 ∂predictive P x y := by
            rw [← Finset.mul_sum, herd51_swap]
        _ ≤ G x := Finset.sum_le_sum (fun k _ => hk k)
    have hG : ∀ x, r ^ 2 * ∫ z, G z ∂predictive P x y ≤ r * G x := by
      intro x
      have := mul_le_mul_of_nonneg_left (hGT x) hr0
      nlinarith
    -- r² T q ≤ r²(2 - r²) q
    have hq : ∀ x, r ^ 2 * ∫ z, q z ∂predictive P x y ≤ r ^ 2 * (2 - r ^ 2) * q x := by
      intro x
      have hI : ∫ z, q z ∂predictive P x y
          = (P.τx / (P.τy + P.τx)) ^ 2 * (x - y) ^ 2 + predVar P + M := by
        rw [hqe, hpolyE]
        have h := hθ x y
        have : thetaHat P x y = y + P.τx / (P.τy + P.τx) * (x - y) := by linarith
        rw [this]; ring
      rw [hI]
      have hWM : predVar P + M = (2 - r ^ 2) * M := by
        rw [hM]; field_simp; ring
      have hαsq : (P.τx / (P.τy + P.τx)) ^ 2 ≤ 2 - r ^ 2 := by
        have := pow_le_one₀ (n := 2) hα0.le hα1
        linarith
      have h1 : (P.τx / (P.τy + P.τx)) ^ 2 * (x - y) ^ 2 + predVar P + M ≤ (2 - r ^ 2) * q x := by
        simp only [hqdef]
        exact herd51_aux2 _ _ _ _ _ hαsq hWM
      have := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
      linarith
    -- F ≤ c G + c' q
    have hb : ∀ x, F x ≤ (2 / (1 - r)) * G x + (2 * P.K * κ ^ 2) * q x := by
      intro x
      have hk : ∀ k : Fin P.K, ((s k x y).1 - muMS P x y) ^ 2 ≤
          (2 / (1 - r)) * (s k x y).2 + 2 * κ ^ 2 * q x := by
        intro k
        have h1 := hvarlb k x y
        have h2 : 0 ≤ r * (1 / n) * ∑ j ∈ Finset.univ.erase k,
            ∫ x', (s j x' y).2 ∂predictive P x y := by
          apply mul_nonneg (by positivity)
          apply Finset.sum_nonneg; intro j _
          exact integral_nonneg (fun x' => ((hs j).2.1 x' y).le)
        have h3 : ((s k x y).1 - thetaHat P x y) ^ 2 ≤ (s k x y).2 / (1 - r) := by
          rw [le_div_iff₀ hr1']; linarith [mul_comm (1 - r) (((s k x y).1 - thetaHat P x y) ^ 2)]
        have h4 : (s k x y).1 - muMS P x y = ((s k x y).1 - thetaHat P x y) - κ * (x - y) := by
          rw [← hmsθ x y]; ring
        rw [h4]
        have h5 : (2 / (1 - r)) * (s k x y).2 = 2 * ((s k x y).2 / (1 - r)) := by ring
        rw [h5]
        simp only [hqdef]
        exact herd51_aux1 _ _ _ _ _ _ hr1' h3 hMpos.le
      calc F x = ∑ k, ((s k x y).1 - muMS P x y) ^ 2 := rfl
        _ ≤ ∑ k : Fin P.K, ((2 / (1 - r)) * (s k x y).2 + 2 * κ ^ 2 * q x) :=
            Finset.sum_le_sum (fun k _ => hk k)
        _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            ring
    have hτ1 : r ^ 2 * (2 - r ^ 2) < 1 := by nlinarith
    have hFle := herd51_iter (fun x => predictive P x y) F G q (r ^ 2) r (r ^ 2 * (2 - r ^ 2))
      (2 / (1 - r)) (2 * P.K * κ ^ 2) (sq_nonneg r) hr0 hr1 (by nlinarith) hτ1 (by positivity)
      (by positivity) hFi hGi hqi hF hG hq hb x₀
    have hsingle : ((s k₀ x₀ y).1 - muMS P x₀ y) ^ 2 ≤ F x₀ :=
      Finset.single_le_sum (f := fun j => ((s j x₀ y).1 - muMS P x₀ y) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ k₀)
    have : ((s k₀ x₀ y).1 - muMS P x₀ y) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  refine ⟨item1, ?_⟩
  intro hgrowth
  have hmcf2 : ∀ (k : Fin P.K) (x y : ℝ), brMean P (closedForm P) k x y = muMS P x y := by
    intro k x y
    have := congrArg Prod.fst (hcf.2 k x y)
    simp only [closedForm] at this
    exact this.symm
  have hvcf : ∀ (k : Fin P.K) (x y : ℝ),
      aCoef P * (x - y) ^ 2 + dCoef P = brVar P (closedForm P) k x y := by
    intro k x y
    have := congrArg Prod.snd (hcf.2 k x y)
    simpa only [closedForm] using this
  have hφe : ∀ y : ℝ, (fun x' => aCoef P * (x' - y) ^ 2 + dCoef P)
      = fun x' => (aCoef P * y ^ 2 + dCoef P) + (-2 * aCoef P * y) * x' + aCoef P * x' ^ 2 := by
    intro y; funext x'; ring
  have hφi : ∀ x y : ℝ, Integrable (fun x' => aCoef P * (x' - y) ^ 2 + dCoef P)
      (predictive P x y) := by
    intro x y; rw [hφe]; exact hpolyI _ _ _ _ _
  have hvdiff : ∀ (k : Fin P.K) (x y : ℝ), (s k x y).2 - (aCoef P * (x - y) ^ 2 + dCoef P)
      = r * (1 / n) * ∑ j ∈ Finset.univ.erase k,
        ∫ x', ((s j x' y).2 - (aCoef P * (x' - y) ^ 2 + dCoef P)) ∂predictive P x y := by
    intro k x y
    rw [hv1 k x y, hvcf k x y]
    unfold brVar
    rw [hmcf2 k x y, ← hm1 k x y, item1 k x y, ← hr, ← hn_def]
    simp only [item1, closedForm]
    have : ∀ j ∈ Finset.univ.erase k,
        ∫ x', ((s j x' y).2 - (aCoef P * (x' - y) ^ 2 + dCoef P)) ∂predictive P x y
        = ∫ x', ((muMS P x y - muMS P x' y) ^ 2 + (s j x' y).2) ∂predictive P x y
          - ∫ x', ((muMS P x y - muMS P x' y) ^ 2 + (aCoef P * (x' - y) ^ 2 + dCoef P))
              ∂predictive P x y := by
      intro j _
      have hsq : Integrable (fun x' => (muMS P x y - muMS P x' y) ^ 2) (predictive P x y) := by
        have e : (fun x' => (muMS P x y - muMS P x' y) ^ 2) = fun x' =>
            (muMS P x y - B * y) ^ 2 + (-2 * (muMS P x y - B * y) * A) * x' + A ^ 2 * x' ^ 2 := by
          funext x'; rw [hms x' y]; ring
        rw [e]; exact hpolyI _ _ _ _ _
      have j1 : Integrable (fun x' => (muMS P x y - muMS P x' y) ^ 2 + (s j x' y).2)
          (predictive P x y) := hsq.add ((hs j).2.2 x y).2.2.1
      have j2 : Integrable
          (fun x' => (muMS P x y - muMS P x' y) ^ 2 + (aCoef P * (x' - y) ^ 2 + dCoef P))
          (predictive P x y) := hsq.add (hφi x y)
      rw [← integral_sub j1 j2]
      congr 1; funext x'; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    ring
  funext k x₀ y
  refine Prod.ext ?_ ?_
  · simp only [closedForm]; exact item1 k x₀ y
  show (s k x₀ y).2 = aCoef P * (x₀ - y) ^ 2 + dCoef P
  -- the growth function
  have hLpos : 0 < Real.log (2 / (1 + r)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith)]; linarith
  set β := Real.sqrt (2 * Real.log (2 / (1 + r)) / predVar P) with hβ
  have hβpos : 0 < β := Real.sqrt_pos.mpr (by positivity)
  have hβsq : predVar P * β ^ 2 / 2 = Real.log (2 / (1 + r)) := by
    rw [hβ, Real.sq_sqrt (by positivity)]; field_simp
  have hlam : Real.exp (predVar P * β ^ 2 / 2) = 2 / (1 + r) := by
    rw [hβsq, Real.exp_log (by positivity)]
  have hτ1 : r * (2 / (1 + r)) < 1 := by
    rw [mul_div_assoc', div_lt_one (by linarith)]; linarith
  choose C N hCN using hgrowth
  choose cL hcL0 hcL using (fun m : ℕ => herd51_growth β y hβpos m)
  set U : ℝ → ℝ := fun x => ∑ j, |(s j x y).2 - (aCoef P * (x - y) ^ 2 + dCoef P)| with hUdef
  set q : ℝ → ℝ := fun x => Real.cosh (β * (x - y)) with hqdef
  set c' : ℝ := ∑ j : Fin P.K, (2 * |C j y| * cL (N j y) + aCoef P * cL 2 + dCoef P * cL 0)
    with hc'
  have hD1 : 0 < (P.τx + P.τy) ^ 2 - r * P.τx ^ 2 := by
    have : r * P.τx ^ 2 < P.τx ^ 2 := by
      have := pow_pos hx 2; nlinarith
    nlinarith [mul_pos hx hy, pow_pos hy 2]
  have ha : 0 ≤ aCoef P := by
    unfold aCoef; rw [← hr]
    have : 0 ≤ 1 - r := by linarith
    positivity
  have hd : 0 < dCoef P := by
    unfold dCoef; rw [← hr]
    positivity
  have hhi : ∀ (j : Fin P.K) (x : ℝ), Integrable
      (fun x' => |(s j x' y).2 - (aCoef P * (x' - y) ^ 2 + dCoef P)|) (predictive P x y) :=
    fun j x => ((((hs j).2.2 x y).2.2.1).sub (hφi x y)).abs
  have hUi : ∀ x, Integrable U (predictive P x y) :=
    fun x => integrable_finsetSum _ (fun j _ => hhi j x)
  have hqi : ∀ x, Integrable q (predictive P x y) := by
    intro x; rw [hpred]; exact (herd51_cosh _ _ _ _).1
  have hF : ∀ x, U x ≤ r * ∫ z, U z ∂predictive P x y := by
    intro x
    have hk : ∀ k : Fin P.K, |(s k x y).2 - (aCoef P * (x - y) ^ 2 + dCoef P)| ≤ r * (1 / n) *
        ∑ j ∈ Finset.univ.erase k,
          ∫ x', |(s j x' y).2 - (aCoef P * (x' - y) ^ 2 + dCoef P)| ∂predictive P x y := by
      intro k
      rw [hvdiff k x y, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r * (1 / n))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
      exact abs_integral_le_integral_abs
    calc U x = ∑ k, |(s k x y).2 - (aCoef P * (x - y) ^ 2 + dCoef P)| := rfl
      _ ≤ ∑ k : Fin P.K, r * (1 / n) * ∑ j ∈ Finset.univ.erase k,
          ∫ x', |(s j x' y).2 - (aCoef P * (x' - y) ^ 2 + dCoef P)| ∂predictive P x y :=
          Finset.sum_le_sum (fun k _ => hk k)
      _ = r * (1 / n) * (n * ∑ j : Fin P.K,
          ∫ x', |(s j x' y).2 - (aCoef P * (x' - y) ^ 2 + dCoef P)| ∂predictive P x y) := by
          rw [← Finset.mul_sum, herd51_swap]
      _ = r * ∫ z, U z ∂predictive P x y := by
          rw [hUdef, integral_finsetSum _ (fun j _ => hhi j x)]
          field_simp
  have hq : ∀ x, r * ∫ z, q z ∂predictive P x y ≤ r * (2 / (1 + r)) * q x := by
    intro x
    rw [hpred, (herd51_cosh _ _ _ _).2, hWr, hlam]
    have hc : Real.cosh (β * (thetaHat P x y - y)) ≤ Real.cosh (β * (x - y)) := by
      rw [Real.cosh_le_cosh, hθ x y, abs_mul, abs_mul, abs_mul]
      have h1 : |P.τx / (P.τy + P.τx)| ≤ 1 := by rw [abs_of_pos hα0]; exact hα1
      have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (x - y))
      have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg β)
      linarith
    have h0 : 0 ≤ r * (2 / (1 + r)) := by positivity
    have := mul_le_mul_of_nonneg_left hc h0
    simp only [hqdef]
    linarith
  have hb : ∀ x, U x ≤ 0 * (fun _ => (0 : ℝ)) x + c' * q x := by
    intro x
    simp only [zero_mul, zero_add]
    rw [hc', Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    have hg := (hs j).2.1 x y
    have hφ : 0 < aCoef P * (x - y) ^ 2 + dCoef P := by positivity
    have h1 : |(s j x y).2 - (aCoef P * (x - y) ^ 2 + dCoef P)|
        ≤ (s j x y).2 + (aCoef P * (x - y) ^ 2 + dCoef P) := by
      rw [abs_le]; constructor <;> linarith
    have hqx : 0 ≤ q x := by simp only [hqdef]; exact (Real.cosh_pos _).le
    have h2 : (s j x y).2 ≤ 2 * |C j y| * cL (N j y) * q x := by
      have := hCN j y x
      have e1 : C j y * (1 + |x| ^ N j y) ≤ |C j y| * (1 + |x| ^ N j y) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      have e2 := mul_le_mul_of_nonneg_left (herd51_aux3 x y (N j y)) (abs_nonneg (C j y))
      have e3 := mul_le_mul_of_nonneg_left (hcL (N j y) x) (by positivity : 0 ≤ 2 * |C j y|)
      calc (s j x y).2 ≤ C j y * (1 + |x| ^ N j y) := this
        _ ≤ |C j y| * (1 + |x| ^ N j y) := e1
        _ ≤ |C j y| * (2 * (1 + |y| + |x - y|) ^ N j y) := e2
        _ = 2 * |C j y| * (1 + |y| + |x - y|) ^ N j y := by ring
        _ ≤ 2 * |C j y| * (cL (N j y) * Real.cosh (β * (x - y))) := e3
        _ = 2 * |C j y| * cL (N j y) * q x := by simp only [hqdef]; ring
    have h3 : aCoef P * (x - y) ^ 2 ≤ aCoef P * cL 2 * q x := by
      have := mul_le_mul_of_nonneg_left ((herd51_aux4 x y).trans (hcL 2 x)) ha
      simp only [hqdef]; linarith
    have h4 : dCoef P ≤ dCoef P * cL 0 * q x := by
      have := hcL 0 x
      simp only [pow_zero] at this
      have := mul_le_mul_of_nonneg_left this hd.le
      simp only [hqdef]; linarith
    rw [add_mul, add_mul]
    linarith
  have hτ0 : 0 ≤ r * (2 / (1 + r)) :=
    mul_nonneg hr0 (div_nonneg (by norm_num) (by linarith))
  have hc'0 : 0 ≤ c' := by
    rw [hc']; apply Finset.sum_nonneg; intro j _
    exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (hcL0 _))
      (mul_nonneg ha (hcL0 2))) (mul_nonneg hd.le (hcL0 0))
  have hZi : ∀ x, Integrable (fun _ : ℝ => (0 : ℝ)) (predictive P x y) :=
    fun x => integrable_const _
  have hZ : ∀ x, r * ∫ z, (fun _ : ℝ => (0 : ℝ)) z ∂predictive P x y ≤ 0 * (fun _ : ℝ => (0 : ℝ)) x := by
    intro x; simp
  have hUle := herd51_iter (fun x => predictive P x y) U (fun _ => (0 : ℝ)) q r 0 (r * (2 / (1 + r)))
    0 c' hr0 (le_refl (0 : ℝ)) zero_lt_one hτ0 hτ1 (le_refl (0 : ℝ)) hc'0
    hUi hZi hqi hF hZ hq hb x₀
  have hsingle : |(s k x₀ y).2 - (aCoef P * (x₀ - y) ^ 2 + dCoef P)| ≤ U x₀ :=
    Finset.single_le_sum (f := fun j => |(s j x₀ y).2 - (aCoef P * (x₀ - y) ^ 2 + dCoef P)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ k)
  have : |(s k x₀ y).2 - (aCoef P * (x₀ - y) ^ 2 + dCoef P)| = 0 :=
    le_antisymm (by linarith) (abs_nonneg _)
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this
