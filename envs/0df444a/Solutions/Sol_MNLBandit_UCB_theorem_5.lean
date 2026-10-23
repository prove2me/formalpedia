-- Prove2me | solution 1 for MNLBandit.UCB.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:48:22.191073+00:00
-- url     : https://prove2.me/submissions/bef6202f-0aab-470e-8947-1f38e5002957

import Mathlib



namespace MNLBandit.UCB

open MeasureTheory ProbabilityTheory

lemma g59_mono_nonneg (f f' : ℝ → ℝ) (hf : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 ≤ x → 0 ≤ f' x) (h0 : f 0 = 0) : ∀ x, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy; exact (hf y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hf y (le_of_lt hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hf y (le_of_lt hy)).deriv]; exact hf' y (le_of_lt hy)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [h0] at this; exact this

-- I1
lemma g59_log_ge1 (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  have := g59_mono_nonneg (fun x => Real.log (1 + x) - 2 * x / (2 + x))
    (fun x => x ^ 2 / ((1 + x) * (2 + x) ^ 2)) ?_ ?_ (by simp) x hx
  · linarith
  · intro y hy
    have h1 : (1 + y) ≠ 0 := by linarith
    have h2 : (2 + y) ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + y)) y := by
      have := ((hasDerivAt_id y).const_add 1).log h1
      simpa using this
    have hd2 : HasDerivAt (fun x => 2 * x / (2 + x)) ((2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
      exact ((hasDerivAt_id y).const_mul 2).div ((hasDerivAt_id y).const_add 2) h2 |>.congr_deriv (by simp)
    exact (hd1.sub hd2).congr_deriv (by field_simp; ring)
  · intro y hy; positivity

-- I4
lemma g59_log_ge4 (x : ℝ) (hx : 0 ≤ x) : x - x^2/2 + x^3/3 - x^4/4 ≤ Real.log (1 + x) := by
  have := g59_mono_nonneg (fun x => Real.log (1 + x) - (x - x^2/2 + x^3/3 - x^4/4))
    (fun x => x ^ 4 / (1 + x)) ?_ ?_ (by simp) x hx
  · linarith
  · intro y hy
    have h1 : (1 + y) ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + y)) y := by
      have := ((hasDerivAt_id y).const_add 1).log h1
      simpa using this
    have hd2 : HasDerivAt (fun x : ℝ => x - x^2/2 + x^3/3 - x^4/4) (1 - y + y^2 - y^3) y := by
      have := ((((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 3 y).div_const 3)).sub ((hasDerivAt_pow 4 y).div_const 4))
      exact this.congr_deriv (by simp)
    exact (hd1.sub hd2).congr_deriv (by field_simp; ring)
  · intro y hy; positivity

-- I5
lemma g59_log_le3 (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x - x^2/2 + x^3/3 := by
  have := g59_mono_nonneg (fun x => (x - x^2/2 + x^3/3) - Real.log (1 + x))
    (fun x => x ^ 3 / (1 + x)) ?_ ?_ (by simp) x hx
  · linarith
  · intro y hy
    have h1 : (1 + y) ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + y)) y := by
      have := ((hasDerivAt_id y).const_add 1).log h1
      simpa using this
    have hd2 : HasDerivAt (fun x : ℝ => x - x^2/2 + x^3/3) (1 - y + y^2) y := by
      have := (((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 3 y).div_const 3))
      exact this.congr_deriv (by simp)
    exact (hd2.sub hd1).congr_deriv (by field_simp; ring)
  · intro y hy; positivity

-- I3' : log(1+z) ≤ z(2+z)/(2(1+z))
lemma g59_log_le2 (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) := by
  have := g59_mono_nonneg (fun x => x * (2 + x) / (2 * (1 + x)) - Real.log (1 + x))
    (fun x => x ^ 2 / (2 * (1 + x) ^ 2)) ?_ ?_ (by simp) x hx
  · linarith
  · intro y hy
    have h1 : (1 + y) ≠ 0 := by linarith
    have h2 : (2 * (1 + y)) ≠ 0 := by positivity
    have hd1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + y)) y := by
      have := ((hasDerivAt_id y).const_add 1).log h1
      simpa using this
    have hd2 : HasDerivAt (fun x : ℝ => x * (2 + x) / (2 * (1 + x)))
        (((1 * (2 + y) + y * 1) * (2 * (1 + y)) - y * (2 + y) * (2 * 1)) / (2 * (1 + y)) ^ 2) y := by
      exact ((hasDerivAt_id y).mul ((hasDerivAt_id y).const_add 2)).div
        (((hasDerivAt_id y).const_add 1).const_mul 2) h2 |>.congr_deriv (by simp)
    exact (hd2.sub hd1).congr_deriv (by field_simp; ring)
  · intro y hy; positivity

lemma g59_log_one_sub (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    -x - x^2 / (2 * (1 - x)) ≤ Real.log (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  have hz := g59_log_le2 (x / (1 - x)) (div_nonneg hx h1.le)
  have e : 1 + x / (1 - x) = (1 - x)⁻¹ := by field_simp; ring
  rw [e, Real.log_inv] at hz
  have e2 : x / (1 - x) * (2 + x / (1 - x)) / (2 * (1 - x)⁻¹) = x + x^2 / (2 * (1 - x)) := by
    field_simp
  rw [e2] at hz; linarith


lemma g59_mgf (p : unitInterval) (hp : p ≠ 0) (θ : ℝ) (hθ : (1 - (p:ℝ)) * Real.exp θ < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (θ * (x : ℝ))) ∂(geometricMeasure p)
      = ENNReal.ofReal ((p:ℝ) / (1 - (1 - (p:ℝ)) * Real.exp θ)) := by
  have hp1 : (p:ℝ) ≤ 1 := p.2.2
  have hp0 : 0 ≤ (p:ℝ) := p.2.1
  set r := (1 - (p:ℝ)) * Real.exp θ with hr
  have hr0 : 0 ≤ r := mul_nonneg (by linarith) (Real.exp_pos θ).le
  rw [geometricMeasure_eq hp, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, lintegral_dirac]
  have : ∀ n : ℕ, ENNReal.ofReal ((1 - (p:ℝ)) ^ n * p) * ENNReal.ofReal (Real.exp (θ * n))
      = ENNReal.ofReal (p * r ^ n) := by
    intro n
    rw [← ENNReal.ofReal_mul (by have : 0 ≤ 1 - (p:ℝ) := by linarith
                                 positivity)]
    congr 1
    rw [hr, mul_pow, mul_comm θ, Real.exp_nat_mul]; ring
  simp_rw [smul_eq_mul, this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_of_lt_one hr0 hθ).mul_left _)]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hθ]; rfl

lemma g59_chernoff (n : ℕ) (p : unitInterval) (hp : p ≠ 0) (θ c : ℝ)
    (hθ : (1 - (p:ℝ)) * Real.exp θ < 1)
    (A : Set (Fin n → ℕ)) (hA : ∀ x ∈ A, θ * (n * c) ≤ θ * ∑ k, (x k : ℝ)) :
    Measure.pi (fun _ : Fin n => geometricMeasure p) A
      ≤ ENNReal.ofReal (Real.exp (-(θ * (n * c)))
          * ((p:ℝ) / (1 - (1 - (p:ℝ)) * Real.exp θ)) ^ n) := by
  set P := Measure.pi (fun _ : Fin n => geometricMeasure p) with hP
  set M := (p:ℝ) / (1 - (1 - (p:ℝ)) * Real.exp θ) with hM
  have hM0 : 0 ≤ M := by
    have : 0 < 1 - (1 - (p:ℝ)) * Real.exp θ := by linarith
    exact div_nonneg p.2.1 this.le
  let g : ℕ → ENNReal := fun x => ENNReal.ofReal (Real.exp (θ * (x : ℝ)))
  let f : (Fin n → ℕ) → ENNReal := fun x => ∏ k, g (x k)
  have hint : ∫⁻ x, f x ∂P = ENNReal.ofReal M ^ n := by
    have hind := iIndepFun_pi (μ := fun _ : Fin n => geometricMeasure p)
      (X := fun _ (x : ℕ) => g x) (fun _ => (measurable_of_countable _).aemeasurable)
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
      (fun i => (measurable_of_countable g).comp (measurable_pi_apply i))]
    have : ∀ i : Fin n, ∫⁻ ω, g (ω i) ∂P = ENNReal.ofReal M := by
      intro i
      rw [(measurePreserving_eval (fun _ : Fin n => geometricMeasure p) i).lintegral_comp
        (measurable_of_countable g)]
      exact g59_mgf p hp θ hθ
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  set ε := ENNReal.ofReal (Real.exp (θ * (n * c))) with hε
  have hsub : A ⊆ {x | ε ≤ f x} := by
    intro x hx
    simp only [Set.mem_setOf_eq, f, g, hε]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => (Real.exp_pos _).le), ← Real.exp_sum,
      ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hA x hx))
  have hmk : ε * P A ≤ ENNReal.ofReal M ^ n := by
    calc ε * P A ≤ ε * P {x | ε ≤ f x} := by gcongr
      _ ≤ ∫⁻ x, f x ∂P := mul_meas_ge_le_lintegral₀ (measurable_of_countable f).aemeasurable ε
      _ = _ := hint
  have hinv : ENNReal.ofReal (Real.exp (-(θ * (n * c)))) * ε = 1 := by
    rw [hε, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  calc P A = ENNReal.ofReal (Real.exp (-(θ * (n * c)))) * (ε * P A) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(θ * (n * c)))) * ENNReal.ofReal M ^ n := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_pow hM0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]


lemma g59_tail (n : ℕ) (p : unitInterval) (hp : p ≠ 0) (s c t : ℝ) (hs : -1 < s)
    (hμs : (1 - (p:ℝ)) / p * s < 1)
    (A : Set (Fin n → ℕ))
    (hA : ∀ x ∈ A, Real.log (1 + s) * (n * c) ≤ Real.log (1 + s) * ∑ k, (x k : ℝ))
    (ht : t ≤ c * Real.log (1 + s) + Real.log (1 - (1 - (p:ℝ)) / p * s)) :
    Measure.pi (fun _ : Fin n => geometricMeasure p) A ≤ ENNReal.ofReal (Real.exp (-(n * t))) := by
  have hp0 : 0 < (p:ℝ) := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  set μ := (1 - (p:ℝ)) / p with hμ
  have hμp : μ * p = 1 - p := by rw [hμ]; field_simp
  have h1s : 0 < 1 + s := by linarith
  have hexp : Real.exp (Real.log (1 + s)) = 1 + s := Real.exp_log h1s
  have hθ : (1 - (p:ℝ)) * Real.exp (Real.log (1 + s)) < 1 := by
    rw [hexp]; nlinarith
  have hpos : 0 < 1 - μ * s := by linarith
  refine le_trans (g59_chernoff n p hp (Real.log (1 + s)) c hθ A hA) ?_
  apply ENNReal.ofReal_le_ofReal
  have hM : (p:ℝ) / (1 - (1 - (p:ℝ)) * Real.exp (Real.log (1 + s)))
      = Real.exp (-Real.log (1 - μ * s)) := by
    rw [hexp, Real.exp_neg, Real.exp_log hpos]
    have : 1 - (1 - (p:ℝ)) * (1 + s) = p * (1 - μ * s) := by linear_combination s * hμp
    rw [this]; field_simp
  rw [hM, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma g59_R1 (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    μ * δ ^ 2 / (2 * (1 + δ) * (1 + μ) ^ 2) ≤
      (1 + δ) * μ * Real.log (1 + δ / (1 + (1 + δ) * μ))
        + Real.log (1 - μ * (δ / (1 + (1 + δ) * μ))) := by
  set a := (1 + δ) * μ with ha
  have ha0 : 0 ≤ a := by positivity
  set s := δ / (1 + a) with hs
  have hs0 : 0 ≤ s := by positivity
  have h1 := g59_log_ge1 s hs0
  have e1 : 1 - μ * s = (1 + μ) / (1 + a) := by rw [hs, ha]; field_simp; ring
  have hpos : 0 < 1 - μ * s := by rw [e1]; positivity
  have h2 := Real.one_sub_inv_le_log_of_pos hpos
  have h3 : a * (2 * s / (2 + s)) ≤ a * Real.log (1 + s) := mul_le_mul_of_nonneg_left h1 ha0
  have key : a * (2 * s / (2 + s)) + (1 - (1 - μ * s)⁻¹) - μ * δ ^ 2 / (2 * (1 + δ) * (1 + μ) ^ 2)
      = δ^3*μ/(2*(δ + 1)*(μ + 1)^2*(2*δ*μ + δ + 2*μ + 2)) := by
    rw [e1, hs, ha]; field_simp; ring
  have hk : 0 ≤ δ^3*μ/(2*(δ + 1)*(μ + 1)^2*(2*δ*μ + δ + 2*μ + 2)) := by positivity
  linarith

lemma g59_R2 (μ δ : ℝ) (hμ : 1 ≤ μ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (δ ^ 2 * μ ^ 2 / (6 * (1 + μ) ^ 2)) * (3 - 2 * δ * μ / (1 + μ)) ≤
      (1 + δ) * μ * Real.log (1 + δ / (1 + (1 + δ) * μ))
        + Real.log (1 - μ * (δ / (1 + (1 + δ) * μ))) := by
  set a := (1 + δ) * μ with ha
  have ha0 : 0 ≤ a := by positivity
  set s := δ / (1 + a) with hs
  have hs0 : 0 ≤ s := by positivity
  set y := μ * δ / (1 + μ) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 := g59_log_ge4 s hs0
  have h2 := g59_log_le3 y hy0
  have e1 : 1 - μ * s = (1 + y)⁻¹ := by rw [hs, ha, hy]; field_simp; ring
  rw [e1, Real.log_inv]
  have h3 := mul_le_mul_of_nonneg_left h1 ha0
  have key : a * (s - s^2/2 + s^3/3 - s^4/4) - (y - y^2/2 + y^3/3)
      - (δ ^ 2 * μ ^ 2 / (6 * (1 + μ) ^ 2)) * (3 - 2 * δ * μ / (1 + μ))
      = δ^2*μ*(μ + 1)^2*(6*δ^3*μ^3 - 2*δ^3*μ^2 + δ^3*μ - 3*δ^3 + 18*δ^2*μ^3 + 14*δ^2*μ^2
          - 3*δ^2*μ + δ^2 + 18*δ*μ^3 + 34*δ*μ^2 + 14*δ*μ - 2*δ + 6*μ^3 + 18*μ^2 + 18*μ + 6)
        / (12*(μ + 1)^3*(δ*μ + μ + 1)^4) := by
    rw [hs, ha, hy]; field_simp; ring
  have hQ : 0 ≤ 6*δ^3*μ^3 - 2*δ^3*μ^2 + δ^3*μ - 3*δ^3 + 18*δ^2*μ^3 + 14*δ^2*μ^2
          - 3*δ^2*μ + δ^2 + 18*δ*μ^3 + 34*δ*μ^2 + 14*δ*μ - 2*δ + 6*μ^3 + 18*μ^2 + 18*μ + 6 := by
    have hd3 : δ^3 ≤ 1 := by nlinarith [pow_le_one₀ hδ.le hδ1.le (n := 3)]
    have hdd : δ^3 ≤ δ^2 := by nlinarith
    have hm2 : μ^2 ≤ μ^3 := by nlinarith
    have hm1 : μ ≤ μ^2 := by nlinarith
    have hd2 : δ^2 ≤ δ := by nlinarith
    nlinarith [mul_nonneg (pow_pos hδ 3).le (sub_nonneg.mpr hm2), mul_nonneg (pow_pos hδ 2).le (sub_nonneg.mpr hm1),
      mul_nonneg hδ.le (sub_nonneg.mpr hm1), pow_pos hδ 3, pow_pos hδ 2]
  have hk : 0 ≤ δ^2*μ*(μ + 1)^2*(6*δ^3*μ^3 - 2*δ^3*μ^2 + δ^3*μ - 3*δ^3 + 18*δ^2*μ^3 + 14*δ^2*μ^2
          - 3*δ^2*μ + δ^2 + 18*δ*μ^3 + 34*δ*μ^2 + 14*δ*μ - 2*δ + 6*μ^3 + 18*μ^2 + 18*μ + 6)
        / (12*(μ + 1)^3*(δ*μ + μ + 1)^4) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) hQ
  linarith

lemma g59_R34 (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (δ ^ 2 * μ / (6 * (1 + μ) ^ 2)) * (3 - 2 * δ * μ / (1 + μ)) ≤
      (1 - δ) * μ * Real.log (1 + -δ / (1 + (1 - δ) * μ))
        + Real.log (1 - μ * (-δ / (1 + (1 - δ) * μ))) ∧
    δ ^ 2 * μ ^ 2 / (2 * (1 + μ) ^ 2) ≤
      (1 - δ) * μ * Real.log (1 + -δ / (1 + (1 - δ) * μ))
        + Real.log (1 - μ * (-δ / (1 + (1 - δ) * μ))) := by
  set a := (1 - δ) * μ with ha
  have ha0 : 0 ≤ a := mul_nonneg (by linarith) hμ
  set x := δ / (1 + a) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one (by positivity)]; nlinarith
  set y := μ * δ / (1 + a) with hy
  have hy0 : 0 ≤ y := by positivity
  have e0 : 1 + -δ / (1 + a) = 1 - x := by rw [hx]; ring
  have e1 : 1 - μ * (-δ / (1 + a)) = 1 + y := by rw [hy]; ring
  rw [e0, e1]
  have h1 := mul_le_mul_of_nonneg_left (g59_log_one_sub x hx0 hx1) ha0
  have h2 := g59_log_ge1 y hy0
  have hA : 0 < 2 * μ + 2 - δ * μ := by nlinarith
  have hB : 0 < μ + 1 - δ * μ := by nlinarith
  have hC : 0 < 1 + a - δ := by rw [ha]; nlinarith
  have h1a : 0 < 1 + a := by linarith
  have ex1 : x^2 / (2 * (1 - x)) = δ^2 / (2 * (1 + a) * (1 + a - δ)) := by
    rw [hx]; field_simp
  have ey : 2 * y / (2 + y) = 2 * μ * δ / (2 * (1 + a) + μ * δ) := by
    rw [hy]; field_simp
  constructor
  · have key0 : ∀ D E F : ℝ, D = 1 + (1 - δ) * μ → E = 2 * D + μ * δ → F = D - δ → D ≠ 0 → F ≠ 0 →
        E ≠ 0 → μ + 1 ≠ 0 →
        (1 - δ) * μ * (-(δ / D) - δ ^ 2 / (2 * D * F)) + 2 * μ * δ / E
        - (δ ^ 2 * μ / (6 * (1 + μ) ^ 2)) * (3 - 2 * δ * μ / (1 + μ))
        = δ^2*μ^2*(2*δ^3*μ^2 - 9*δ^2*μ^2 - 9*δ^2*μ - 6*δ*μ^3 - 2*δ*μ^2 + 14*δ*μ + 10*δ
            + 6*μ^3 + 18*μ^2 + 18*μ + 6) / (6*(μ + 1)^3*E*D) := by
      intro D E F hD hE hF h1 h2 h3 h4
      have h4' : 1 + μ ≠ 0 := by rwa [add_comm]
      field_simp
      subst hE hF hD
      ring
    have key : a * (-x - x^2 / (2 * (1 - x))) + 2 * y / (2 + y)
        - (δ ^ 2 * μ / (6 * (1 + μ) ^ 2)) * (3 - 2 * δ * μ / (1 + μ))
        = δ^2*μ^2*(2*δ^3*μ^2 - 9*δ^2*μ^2 - 9*δ^2*μ - 6*δ*μ^3 - 2*δ*μ^2 + 14*δ*μ + 10*δ
            + 6*μ^3 + 18*μ^2 + 18*μ + 6) / (6*(μ + 1)^3*(2 * (1 + a) + μ * δ)*(1 + a)) := by
      rw [ex1, ey, hx]
      exact key0 (1 + a) (2 * (1 + a) + μ * δ) (1 + a - δ) (by rw [ha]) rfl rfl h1a.ne' hC.ne'
        (by have : 0 ≤ μ * δ := by positivity
            linarith) (by linarith)
    have hR : 0 ≤ 2*δ^3*μ^2 - 9*δ^2*μ^2 - 9*δ^2*μ - 6*δ*μ^3 - 2*δ*μ^2 + 14*δ*μ + 10*δ
            + 6*μ^3 + 18*μ^2 + 18*μ + 6 := by
      have hd2 : δ^2 ≤ δ := by nlinarith
      nlinarith [mul_nonneg (pow_pos hδ 3).le (sq_nonneg μ), mul_nonneg (pow_nonneg hμ 3) (sub_nonneg.mpr hδ1.le),
        mul_nonneg (sq_nonneg μ) (sub_nonneg.mpr hd2), mul_nonneg hμ (sub_nonneg.mpr hd2), sq_nonneg μ,
        mul_nonneg (sq_nonneg μ) hδ.le, mul_nonneg hμ hδ.le]
    have hk : 0 ≤ δ^2*μ^2*(2*δ^3*μ^2 - 9*δ^2*μ^2 - 9*δ^2*μ - 6*δ*μ^3 - 2*δ*μ^2 + 14*δ*μ + 10*δ
            + 6*μ^3 + 18*μ^2 + 18*μ + 6) / (6*(μ + 1)^3*(2 * (1 + a) + μ * δ)*(1 + a)) := by
      apply div_nonneg (mul_nonneg (by positivity) hR)
      have p2 : 0 < 2 * (1 + a) + μ * δ := by have : 0 ≤ μ * δ := by positivity
                                              linarith
      exact (mul_pos (mul_pos (by positivity) p2) h1a).le
    linarith
  · have key0 : ∀ D E F : ℝ, D = 1 + (1 - δ) * μ → E = 2 * D + μ * δ → F = D - δ → D ≠ 0 → F ≠ 0 →
        E ≠ 0 → μ + 1 ≠ 0 →
        (1 - δ) * μ * (-(δ / D) - δ ^ 2 / (2 * D * F)) + 2 * μ * δ / E
        - δ ^ 2 * μ ^ 2 / (2 * (1 + μ) ^ 2)
        = δ^2*μ*(-(δ^2*μ^3 - δ*μ^3 + δ*μ - 2*μ^2 - 4*μ - 2)) / (2*(μ + 1)^2*E*D) := by
      intro D E F hD hE hF h1 h2 h3 h4
      have h4' : 1 + μ ≠ 0 := by rwa [add_comm]
      field_simp
      subst hE hF hD
      ring
    have key : a * (-x - x^2 / (2 * (1 - x))) + 2 * y / (2 + y)
        - δ ^ 2 * μ ^ 2 / (2 * (1 + μ) ^ 2)
        = δ^2*μ*(-(δ^2*μ^3 - δ*μ^3 + δ*μ - 2*μ^2 - 4*μ - 2)) / (2*(μ + 1)^2*(2 * (1 + a) + μ * δ)*(1 + a)) := by
      rw [ex1, ey, hx]
      exact key0 (1 + a) (2 * (1 + a) + μ * δ) (1 + a - δ) (by rw [ha]) rfl rfl h1a.ne' hC.ne'
        (by have : 0 ≤ μ * δ := by positivity
            linarith) (by linarith)
    have hR : 0 ≤ -(δ^2*μ^3 - δ*μ^3 + δ*μ - 2*μ^2 - 4*μ - 2) := by
      have q1 : 0 ≤ δ * μ ^ 3 * (1 - δ) := mul_nonneg (mul_nonneg hδ.le (pow_nonneg hμ 3)) (sub_nonneg.mpr hδ1.le)
      have q2 : δ * μ ≤ μ := by nlinarith
      have q3 : 0 ≤ μ ^ 2 := sq_nonneg μ
      have e : -(δ^2*μ^3 - δ*μ^3 + δ*μ - 2*μ^2 - 4*μ - 2) = δ * μ ^ 3 * (1 - δ) + (μ - δ * μ) + 2 * μ ^ 2 + 3 * μ + 2 := by ring
      rw [e]; linarith
    have hk : 0 ≤ δ^2*μ*(-(δ^2*μ^3 - δ*μ^3 + δ*μ - 2*μ^2 - 4*μ - 2)) / (2*(μ + 1)^2*(2 * (1 + a) + μ * δ)*(1 + a)) := by
      apply div_nonneg (mul_nonneg (by positivity) hR)
      have p2 : 0 < 2 * (1 + a) + μ * δ := by have : 0 ≤ μ * δ := by positivity
                                              linarith
      exact (mul_pos (mul_pos (by positivity) p2) h1a).le
    linarith


theorem theorem_5_core (n : ℕ) (hn : 1 ≤ n) (p : unitInterval) (hp : p ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    let μ : ℝ := (1 - (p : ℝ)) / (p : ℝ)
    let P : Measure (Fin n → ℕ) := Measure.pi (fun _ : Fin n => geometricMeasure p)
    let Xbar : (Fin n → ℕ) → ℝ := fun x => (∑ k, (x k : ℝ)) / (n : ℝ)
    (μ ≤ 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * μ * δ ^ 2) / (2 * (1 + δ) * (1 + μ) ^ 2)))) ∧
    (1 ≤ μ → δ < 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2 / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (μ ≤ 1 → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (1 ≤ μ → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2) / (2 * (1 + μ) ^ 2)))) := by
  intro μ P Xbar
  have hp0 : 0 < (p:ℝ) := lt_of_le_of_ne p.2.1 (fun h => hp (Subtype.ext h.symm))
  have hp1 : (p:ℝ) ≤ 1 := p.2.2
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hp0.le
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hsum0 : ∀ x : Fin n → ℕ, 0 ≤ ∑ k, (x k : ℝ) :=
    fun x => Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  have upper : ∀ t, t ≤ (1 + δ) * μ * Real.log (1 + δ / (1 + (1 + δ) * μ))
      + Real.log (1 - μ * (δ / (1 + (1 + δ) * μ))) →
      P {x | Xbar x > (1 + δ) * μ} ≤ ENNReal.ofReal (Real.exp (-(n * t))) := by
    intro t ht
    have ha0 : 0 ≤ (1 + δ) * μ := by positivity
    have hs0 : 0 ≤ δ / (1 + (1 + δ) * μ) := by positivity
    apply g59_tail n p hp (δ / (1 + (1 + δ) * μ)) ((1 + δ) * μ) t (by linarith) ?_ _ ?_ ht
    · show μ * (δ / (1 + (1 + δ) * μ)) < 1
      rw [mul_div_assoc', div_lt_one (by positivity)]; nlinarith
    · intro x hx
      simp only [Set.mem_setOf_eq, Xbar] at hx
      rw [gt_iff_lt, lt_div_iff₀ hnpos] at hx
      apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by linarith))
      linarith
  have lower : δ < 1 → ∀ t, t ≤ (1 - δ) * μ * Real.log (1 + -δ / (1 + (1 - δ) * μ))
      + Real.log (1 - μ * (-δ / (1 + (1 - δ) * μ))) →
      P {x | Xbar x < (1 - δ) * μ} ≤ ENNReal.ofReal (Real.exp (-(n * t))) := by
    intro hδ1 t ht
    have ha0 : 0 ≤ (1 - δ) * μ := mul_nonneg (by linarith) hμ0
    have hD : 0 < 1 + (1 - δ) * μ := by linarith
    have hx0 : 0 ≤ δ / (1 + (1 - δ) * μ) := by positivity
    have hx1 : δ / (1 + (1 - δ) * μ) < 1 := by rw [div_lt_one hD]; linarith
    have es : -δ / (1 + (1 - δ) * μ) = -(δ / (1 + (1 - δ) * μ)) := by ring
    apply g59_tail n p hp (-δ / (1 + (1 - δ) * μ)) ((1 - δ) * μ) t (by rw [es]; linarith) ?_ _ ?_ ht
    · show μ * (-δ / (1 + (1 - δ) * μ)) < 1
      rw [es]; nlinarith
    · intro x hx
      simp only [Set.mem_setOf_eq, Xbar] at hx
      rw [div_lt_iff₀ hnpos] at hx
      apply mul_le_mul_of_nonpos_left _ (Real.log_nonpos (by rw [es]; linarith) (by rw [es]; linarith))
      linarith
  have empty : 1 ≤ δ → P {x | Xbar x < (1 - δ) * μ} = 0 := by
    intro hδ1
    have : {x | Xbar x < (1 - δ) * μ} = (∅ : Set (Fin n → ℕ)) := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      simp only [Set.mem_setOf_eq, Xbar] at hx
      have h1 : 0 ≤ (∑ k, (x k : ℝ)) / n := div_nonneg (hsum0 x) hnpos.le
      have h2 : (1 - δ) * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hμ0
      linarith
    rw [this, measure_empty]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _
    refine le_trans (upper _ (g59_R1 μ δ hμ0 hδ)) ?_
    apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.mpr; apply le_of_eq; ring
  · intro hμ1 hδ1
    refine le_trans (upper _ (g59_R2 μ δ hμ1 hδ hδ1)) ?_
    apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.mpr; apply le_of_eq; ring
  · intro _
    by_cases hδ1 : δ < 1
    · refine le_trans (lower hδ1 _ (g59_R34 μ δ hμ0 hδ hδ1).1) ?_
      apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.mpr; apply le_of_eq; ring
    · rw [empty (by linarith)]; exact zero_le
  · intro _
    by_cases hδ1 : δ < 1
    · refine le_trans (lower hδ1 _ (g59_R34 μ δ hμ0 hδ hδ1).2) ?_
      apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.mpr; apply le_of_eq; ring
    · rw [empty (by linarith)]; exact zero_le

end MNLBandit.UCB

open MNLBandit.UCB
open MeasureTheory ProbabilityTheory

theorem solution (n : ℕ) (hn : 1 ≤ n) (p : unitInterval) (hp : p ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    let μ : ℝ := (1 - (p : ℝ)) / (p : ℝ)
    let P : Measure (Fin n → ℕ) := Measure.pi (fun _ : Fin n => geometricMeasure p)
    let Xbar : (Fin n → ℕ) → ℝ := fun x => (∑ k, (x k : ℝ)) / (n : ℝ)
    (μ ≤ 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * μ * δ ^ 2) / (2 * (1 + δ) * (1 + μ) ^ 2)))) ∧
    (1 ≤ μ → δ < 1 → P {x | Xbar x > (1 + δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2 / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (μ ≤ 1 → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ / (6 * (1 + μ) ^ 2))
          * (3 - 2 * δ * μ / (1 + μ))))) ∧
    (1 ≤ μ → P {x | Xbar x < (1 - δ) * μ} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) * δ ^ 2 * μ ^ 2) / (2 * (1 + μ) ^ 2)))) := by
  exact theorem_5_core n hn p hp δ hδ
