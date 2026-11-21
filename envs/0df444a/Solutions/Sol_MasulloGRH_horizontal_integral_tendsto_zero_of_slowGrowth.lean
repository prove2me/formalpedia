-- Prove2me | solution 1 for MasulloGRH.horizontal_integral_tendsto_zero_of_slowGrowth
-- status  : ACCEPTED   (disprove)
-- author  : @koffie
-- created : 2026-11-21T00:01:43.587863+00:00
-- url     : https://prove2.me/submissions/d8a8026f-506e-4e2c-ac56-4568fe0c633d

import Definitions.Def_MasulloGRH_MellinRpos
import Definitions.Def_MasulloGRH_SlowGrowthNearPoles

/-!
Counterexample to Masullo, Lemma B.3.1.2 (p. 604–605), as stated with Definition B.3.1.1.

On the strip `0 < Re s < 1` take
* `f(s) = exp(-i · exp(iπ(s - 4/5)/(7/10)))` (entire, `|f| = 1` on `Re s = 1/10` and `Re s = 4/5`),
* `T_k = ±(7/(10π)) log log(|k| + 3)` (sign of `k`, with `+` for `k = 0`),
* `Φ(s) = exp(s²)` (entire and uniformly Schwartz on every vertical strip).
Then `f` has slow growth near its poles, but along `k → -∞` the integrals
`∫₀¹ |f Φ|(σ + i T_k) dσ` stay `≥ 1/25`.
-/

open Complex Filter Topology MasulloGRH

namespace CounterexB312

noncomputable def L : ℝ := 7 / 10

noncomputable def F (s : ℂ) : ℂ :=
  Complex.exp (-I * Complex.exp (I * (Real.pi : ℂ) * (s - 4 / 5) / (L : ℂ)))

noncomputable def Φ (s : ℂ) : ℂ := Complex.exp (s ^ 2)

noncomputable def c : ℝ := 7 / (10 * Real.pi)

noncomputable def ll (k : ℤ) : ℝ := Real.log (Real.log (|(k : ℝ)| + 3))

noncomputable def T (k : ℤ) : ℝ := (if 0 ≤ k then (1 : ℝ) else -1) * c * ll k

lemma L_pos : 0 < L := by norm_num [L]

lemma c_pos : 0 < c := by unfold c; positivity

lemma log_ge_one (k : ℤ) : 1 ≤ Real.log (|(k : ℝ)| + 3) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) ≤ |(k : ℝ)| := abs_nonneg _
  linarith

lemma ll_nonneg (k : ℤ) : 0 ≤ ll k := Real.log_nonneg (log_ge_one k)

lemma exp_ll (k : ℤ) : Real.exp (ll k) = Real.log (|(k : ℝ)| + 3) :=
  Real.exp_log (by linarith [log_ge_one k])

lemma abs_T (k : ℤ) : |T k| = c * ll k := by
  unfold T
  split_ifs
  · rw [one_mul, abs_of_nonneg (mul_nonneg c_pos.le (ll_nonneg k))]
  · rw [neg_one_mul, neg_mul, abs_neg, abs_of_nonneg (mul_nonneg c_pos.le (ll_nonneg k))]

lemma F_differentiable : Differentiable ℂ F := by
  unfold F; fun_prop

lemma Φ_differentiable : Differentiable ℂ Φ := by
  unfold Φ; fun_prop

/-- The modulus of `F` on horizontal coordinates. -/
lemma norm_F (σ t : ℝ) : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ =
    Real.exp (Real.exp (-(Real.pi * t) / L) * Real.sin (Real.pi * (σ - 4 / 5) / L)) := by
  unfold F
  rw [Complex.norm_exp]
  congr 1
  have hw : I * (Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * I - 4 / 5) / (L : ℂ) =
      (((-(Real.pi * t) / L : ℝ)) : ℂ) + (((Real.pi * (σ - 4 / 5) / L : ℝ)) : ℂ) * I := by
    apply Complex.ext <;>
      simp [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hw]
  rw [show -I * Complex.exp (((-(Real.pi * t) / L : ℝ)) + ((Real.pi * (σ - 4 / 5) / L : ℝ)) * I) =
      -I * (Complex.exp ((-(Real.pi * t) / L : ℝ)) *
        Complex.exp (((Real.pi * (σ - 4 / 5) / L : ℝ)) * I)) by rw [Complex.exp_add]]
  rw [← Complex.ofReal_exp, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im]
  try ring

lemma norm_Φ (σ t : ℝ) : ‖Φ ((σ : ℂ) + (t : ℂ) * I)‖ = Real.exp (σ ^ 2 - t ^ 2) := by
  unfold Φ
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im]
  try ring

lemma exp_T_neg {k : ℤ} (hk : k < 0) : Real.exp (-(Real.pi * T k) / L) = Real.log (|(k : ℝ)| + 3) := by
  have : -(Real.pi * T k) / L = ll k := by
    unfold T c L
    rw [if_neg (by omega)]
    field_simp
  rw [this, exp_ll]

lemma exp_T_nonneg {k : ℤ} (hk : 0 ≤ k) : Real.exp (-(Real.pi * T k) / L) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : 0 ≤ Real.pi * T k / L := by
    unfold T
    rw [if_pos hk, one_mul]
    exact div_nonneg (mul_nonneg Real.pi_pos.le (mul_nonneg c_pos.le (ll_nonneg k))) L_pos.le
  rw [neg_div]
  linarith

lemma abs_int_ge_one {k : ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ |(k : ℝ)| := by
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hk

lemma slowGrowth : HasSlowGrowthNearPoles F 0 1 T := by
  refine ⟨fun z _ => (F_differentiable.analyticAt z).meromorphicAt, ?_, ?_, ?_⟩
  · refine ⟨1, one_pos, ?_, ?_, ?_, ?_⟩
    · intro k
      have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
          c * Real.log (Real.log (x + 3)) ≤ c * Real.log (Real.log (y + 3)) := by
        intro x y hx hxy
        apply mul_le_mul_of_nonneg_left _ c_pos.le
        have h1 : 1 ≤ Real.log (x + 3) := by
          have := log_ge_one 0
          simp only [Int.cast_zero, abs_zero, zero_add] at this
          exact this.trans (Real.log_le_log (by norm_num) (by linarith))
        exact Real.log_le_log (by linarith) (Real.log_le_log (by linarith) (by linarith))
      simp only [abs_T, ll]
      constructor
      · apply hmono _ _ (abs_nonneg _)
        push_cast
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        linarith
      · apply hmono _ _ (abs_nonneg _)
        push_cast
        rw [abs_neg, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        linarith
    · simp only [abs_T]
      apply Tendsto.const_mul_atTop c_pos
      unfold ll
      apply Real.tendsto_log_atTop.comp
      apply Real.tendsto_log_atTop.comp
      apply tendsto_atTop_add_const_right
      have h1 : Tendsto (fun k : ℤ => |k|) cofinite atTop := by
        rw [Int.cofinite_eq]
        exact tendsto_sup.2 ⟨tendsto_abs_atBot_atTop, tendsto_abs_atTop_atTop⟩
      have h2 := (tendsto_intCast_atTop_atTop (R := ℝ)).comp h1
      refine h2.congr fun k => ?_
      simp [Int.cast_abs]
    · apply Asymptotics.IsBigO.of_bound (4 * c)
      filter_upwards [eventually_cofinite_ne 0] with k hk
      have hk1 := abs_int_ge_one hk
      rw [Real.norm_eq_abs, abs_T, Real.rpow_one, Real.norm_eq_abs, abs_abs]
      have h1 : ll k ≤ |(k : ℝ)| + 3 := by
        unfold ll
        have := log_ge_one k
        calc Real.log (Real.log (|(k : ℝ)| + 3)) ≤ Real.log (|(k : ℝ)| + 3) :=
              Real.log_le_self (by linarith)
          _ ≤ |(k : ℝ)| + 3 := Real.log_le_self (by positivity)
      nlinarith [c_pos]
    · intro k
      exact ⟨1, one_pos, F_differentiable.differentiableOn⟩
  · refine ⟨1, 4, one_pos, by norm_num, ?_⟩
    intro k hk σ _ _
    have hk1 := abs_int_ge_one hk
    rw [norm_F, Real.rpow_one]
    have hE : 0 < Real.exp (-(Real.pi * T k) / L) := Real.exp_pos _
    have hs : Real.exp (-(Real.pi * T k) / L) * Real.sin (Real.pi * (σ - 4 / 5) / L) ≤
        Real.exp (-(Real.pi * T k) / L) := by
      nlinarith [Real.sin_le_one (Real.pi * (σ - 4 / 5) / L)]
    refine (Real.exp_le_exp.2 hs).trans ?_
    rcases lt_or_ge k 0 with hneg | hnn
    · rw [exp_T_neg hneg, Real.exp_log (by positivity)]
      linarith
    · have := Real.exp_le_exp.2 (exp_T_nonneg hnn)
      have he := Real.exp_one_lt_d9
      linarith
  · refine ⟨1 / 10, 1 / 5, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · exact F_differentiable.continuous.comp (by fun_prop)
    · exact F_differentiable.continuous.comp (by fun_prop)
    · refine ⟨1, 0, fun t => ⟨?_, ?_⟩⟩
      · rw [norm_F]
        have : Real.pi * ((0 + 1 / 10 : ℝ) - 4 / 5) / L = -Real.pi := by
          unfold L; ring
        rw [this, Real.sin_neg, Real.sin_pi]
        simp
      · rw [norm_F]
        have : Real.pi * ((1 - 1 / 5 : ℝ) - 4 / 5) / L = 0 := by
          unfold L; ring
        rw [this, Real.sin_zero]
        simp
    · intro t
      exact ⟨F_differentiable.analyticAt _, F_differentiable.analyticAt _⟩

lemma schwartzΦ : UniformlySchwartzOnStrip Φ (0 - 1) (1 + 1) := by
  intro ε hε _ N _
  refine ⟨Real.exp 4 * N.factorial, by positivity, 1, ?_⟩
  intro s hs1 hs2 hY
  have hre : s.re ^ 2 ≤ 4 := by nlinarith
  have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  rw [show Φ s = Φ ((s.re : ℂ) + (s.im : ℂ) * I) by rw [← hs], norm_Φ]
  have hy : 0 < |s.im| := by linarith
  have h1 : Real.exp (s.re ^ 2 - s.im ^ 2) ≤ Real.exp 4 * Real.exp (-|s.im|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : |s.im| ≤ s.im ^ 2 := by
      rw [← sq_abs]; nlinarith
    linarith
  have h2 : Real.exp (-|s.im|) ≤ N.factorial / |s.im| ^ N := by
    rw [Real.exp_neg, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (Real.exp_pos _)]
    have := Real.pow_div_factorial_le_exp (|s.im|) (abs_nonneg s.im) N
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  calc Real.exp (s.re ^ 2 - s.im ^ 2) ≤ Real.exp 4 * Real.exp (-|s.im|) := h1
    _ ≤ Real.exp 4 * (N.factorial / |s.im| ^ N) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp 4 * N.factorial / |s.im| ^ N := by ring

lemma sin_lower {σ : ℝ} (h1 : 24 / 25 ≤ σ) (h2 : σ ≤ 1) :
    3 / 5 ≤ Real.sin (Real.pi * (σ - 4 / 5) / L) := by
  set x := Real.pi * (σ - 4 / 5) / L with hx
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hxl : 3.14 * (4 / 25) / (7 / 10) ≤ x := by
    rw [hx]; unfold L
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hxu : x ≤ 3.15 * (1 / 5) / (7 / 10) := by
    rw [hx]; unfold L
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hx0 : 0 < x := by norm_num at hxl; linarith
  have hx1 : x ≤ 1 := by norm_num at hxu; linarith
  have := Real.sin_gt_sub_cube hx0
  norm_num at hxl hxu
  nlinarith [sq_nonneg x, mul_pos hx0 hx0]

/-- The integrand is at least `1` on `[24/25, 1]` for `k < 0`. -/
lemma integrand_ge_one {k : ℤ} (hk : k < 0) {σ : ℝ} (h1 : 24 / 25 ≤ σ) (h2 : σ ≤ 1) :
    1 ≤ ‖F ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖ := by
  rw [norm_mul, norm_F, norm_Φ, exp_T_neg hk, ← Real.exp_add]
  apply Real.one_le_exp
  set E := Real.log (|(k : ℝ)| + 3) with hE
  have hE1 : 1 ≤ E := log_ge_one k
  have hsin := sin_lower h1 h2
  -- `T k ^ 2 = c^2 (log E)^2 ≤ (1/18) * 2E`
  have hT : T k ^ 2 = c ^ 2 * ll k ^ 2 := by
    rw [← sq_abs, abs_T]; ring
  have hy0 := ll_nonneg k
  have hy : ll k ^ 2 ≤ 2 * E := by
    have := Real.quadratic_le_exp_of_nonneg hy0
    rw [exp_ll] at this
    nlinarith
  have hc : c ^ 2 ≤ 1 / 18 := by
    unfold c
    have hp := Real.pi_gt_three
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have : T k ^ 2 ≤ E / 9 := by
    rw [hT]
    calc c ^ 2 * ll k ^ 2 ≤ 1 / 18 * (2 * E) :=
          mul_le_mul hc hy (sq_nonneg _) (by norm_num)
      _ = E / 9 := by ring
  nlinarith [sq_nonneg σ]

lemma integrand_continuous (k : ℤ) :
    Continuous (fun σ : ℝ => ‖F ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖) := by
  have hF := F_differentiable.continuous
  have hΦ := Φ_differentiable.continuous
  fun_prop

lemma integral_ge {k : ℤ} (hk : k < 0) :
    1 / 25 ≤ ∫ σ in (0 : ℝ)..1, ‖F ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖ := by
  set g := fun σ : ℝ => ‖F ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖ with hg
  have hc := integrand_continuous k
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 24 / 25)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : 0 ≤ ∫ σ in (0 : ℝ)..24 / 25, g σ :=
    intervalIntegral.integral_nonneg (by norm_num) fun _ _ => norm_nonneg _
  have h2 : ∫ σ in (24 / 25 : ℝ)..1, (1 : ℝ) ≤ ∫ σ in (24 / 25 : ℝ)..1, g σ :=
    intervalIntegral.integral_mono_on (by norm_num) (by simp) (hc.intervalIntegrable _ _)
      fun σ hσ => integrand_ge_one hk hσ.1 hσ.2
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
  norm_num at h2
  linarith

end CounterexB312

open CounterexB312 in
theorem solution : ¬ (∀ (a b : ℝ) (hab : a < b) (f : ℂ → ℂ) (T : ℤ → ℝ)
    (hf : HasSlowGrowthNearPoles f a b T) (ε : ℝ) (hε : 0 < ε) (Φ : ℂ → ℂ)
    (hΦd : DifferentiableOn ℂ Φ (openStrip (a - ε) (b + ε)))
    (hΦ : UniformlySchwartzOnStrip Φ (a - ε) (b + ε)),
    Tendsto (fun k : ℤ => ∫ σ in a..b,
        ‖f ((σ : ℂ) - (T k : ℂ) * I) * Φ ((σ : ℂ) - (T k : ℂ) * I)‖) cofinite (𝓝 0) ∧
    Tendsto (fun k : ℤ => ∫ σ in a..b,
        ‖f ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖) cofinite (𝓝 0)) := by
  intro h
  have h2 := (h 0 1 one_pos F CounterexB312.T slowGrowth 1 one_pos CounterexB312.Φ
    Φ_differentiable.differentiableOn schwartzΦ).2
  have hev := h2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 25 by norm_num))
  rw [Int.cofinite_eq] at hev
  obtain ⟨k₀, hk₀⟩ := (eventually_sup.1 hev).1.exists_forall_of_atBot
  have := hk₀ (min k₀ (-1)) (min_le_left _ _)
  have hneg : min k₀ (-1) < 0 := by omega
  linarith [integral_ge hneg]
