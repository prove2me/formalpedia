-- Prove2me | solution 1 for GradErrors.Deterministic.liminf_grad_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:22:36.500579+00:00
-- url     : https://prove2.me/submissions/a1efe30a-0087-4a1c-87bd-e393176a6b72

import Mathlib

open Filter Topology NNReal InnerProductSpace


namespace GradErrors.Deterministic

lemma ge_line_deriv {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (hd : Differentiable ℝ h)
    (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • v)) ⟪gradient h (x + t • v), v⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hf := (hd (x + t • v)).hasFDerivAt
  have := hf.comp_hasDerivAt t hl
  have e : fderiv ℝ h (x + t • v) v = ⟪gradient h (x + t • v), v⟫_ℝ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [← e]; exact this

lemma ge_descent {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (hd : Differentiable ℝ h)
    (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖) (x y : EuclideanSpace ℝ (Fin n)) :
    h y ≤ h x + ⟪gradient h x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  set ψ : ℝ → ℝ := fun t => h (x + t • v) - t * ⟪gradient h x, v⟫_ℝ - L / 2 * t ^ 2 * ‖v‖ ^ 2
    with hψ
  have hψd : ∀ t, HasDerivAt ψ (⟪gradient h (x + t • v), v⟫_ℝ - ⟪gradient h x, v⟫_ℝ
      - L * t * ‖v‖ ^ 2) t := by
    intro t
    have h1 := ge_line_deriv h hd x v t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient h x, v⟫_ℝ) ⟪gradient h x, v⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient h x, v⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have := (hp.const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      exact this.congr_deriv (by ring)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hcs : ⟪gradient h (x + t • v) - gradient h x, v⟫_ℝ ≤
          ‖gradient h (x + t • v) - gradient h x‖ * ‖v‖ := real_inner_le_norm _ _
      have hlip := hL (x + t • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hlip
      rw [inner_sub_left] at hcs
      have := mul_le_mul_of_nonneg_right hlip (norm_nonneg v)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h01
  rw [hv, add_sub_cancel] at h01
  linarith

/-- γ → 0 -/
lemma ge_gamma_small (γ : ℕ → ℝ) (hγ : ∀ t, 0 < γ t) (hsq : Summable (fun t => γ t ^ 2))
    (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ t in atTop, γ t ≤ δ := by
  have := hsq.tendsto_atTop_zero
  filter_upwards [this.eventually (gt_mem_nhds (by positivity : (0:ℝ) < δ ^ 2))] with t ht
  nlinarith [hγ t]

theorem eventual_descent_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ)
    (c₁ c₂ p q : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hp : 0 < p) (hq : 0 < q)
    (hx : ∀ t, x (t + 1) = x t + γ t • (s t + w t))
    (h22a : ∀ t, c₁ * ‖gradient f (x t)‖ ^ 2 ≤ -⟪gradient f (x t), s t⟫_ℝ)
    (h22b : ∀ t, ‖s t‖ ≤ c₂ * (1 + ‖gradient f (x t)‖))
    (h23 : ∀ t, ‖w t‖ ≤ γ t * (q + p * ‖gradient f (x t)‖))
    (hγ : ∀ t, 0 < γ t)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∃ β₂ : ℝ, 0 < β₂ ∧ ∃ T : ℕ, ∀ t ≥ T,
      f (x (t + 1)) ≤ f (x t) - γ t * β₁ * ‖gradient f (x t)‖ ^ 2 + γ t ^ 2 * β₂ := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  set Lr : ℝ := (L : ℝ) with hLr
  have hL0 : 0 ≤ Lr := L.2
  have hLip : ∀ a b, ‖gradient f a - gradient f b‖ ≤ Lr * ‖a - b‖ := by
    intro a b
    have := hL.dist_le_mul a b
    simpa [dist_eq_norm] using this
  set M := c₂ + q + p with hM
  set B := Lr * M ^ 2 + q / 2 + p with hB
  have hBpos : 0 < B := by positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((ge_gamma_small γ hγ hsq 1 one_pos).and
    (ge_gamma_small γ hγ hsq (c₁ / (2 * B)) (by positivity)))
  refine ⟨c₁ / 2, by positivity, Lr * M ^ 2 + q / 2 + 1, by positivity, T, fun t ht => ?_⟩
  obtain ⟨hg1, hg2⟩ := hT t ht
  have hgB : γ t * B ≤ c₁ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hg2; nlinarith
  set G := ‖gradient f (x t)‖ with hG
  set g := gradient f (x t)
  set a := ‖s t‖
  set b := ‖w t‖
  set c := γ t with hc
  have hc0 : 0 < c := hγ t
  have hG0 : 0 ≤ G := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ha0 : 0 ≤ a := norm_nonneg _
  have hdes := ge_descent f hd Lr hL0 hLip (x t) (x (t + 1))
  have hdiff : x (t + 1) - x t = c • (s t + w t) := by rw [hx t]; abel
  rw [hdiff, inner_smul_right, inner_add_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    at hdes
  have hgw : ⟪g, w t⟫_ℝ ≤ G * b := real_inner_le_norm _ _
  have hsw : ‖s t + w t‖ ≤ a + b := norm_add_le _ _
  have hsa := h22a t
  have hsb : a ≤ c₂ * (1 + G) := h22b t
  have hwb : b ≤ c * (q + p * G) := h23 t
  have hwb1 : b ≤ q + p * G := by
    have : c * (q + p * G) ≤ 1 * (q + p * G) :=
      mul_le_mul_of_nonneg_right hg1 (by positivity)
    linarith
  have hab : a + b ≤ M * (1 + G) := by rw [hM]; nlinarith
  have hn2 : ‖s t + w t‖ ^ 2 ≤ 2 * M ^ 2 * (1 + G ^ 2) := by
    have h1 : ‖s t + w t‖ ≤ M * (1 + G) := hsw.trans hab
    have h2 : ‖s t + w t‖ ^ 2 ≤ (M * (1 + G)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (1 - G)]
  have hq1 : c * (G * b) ≤ c ^ 2 * (q / 2 * (1 + G ^ 2) + p * G ^ 2) := by
    have : G * b ≤ G * (c * (q + p * G)) := mul_le_mul_of_nonneg_left hwb hG0
    have h2 : G * (q + p * G) ≤ q / 2 * (1 + G ^ 2) + p * G ^ 2 := by
      nlinarith [sq_nonneg (1 - G)]
    calc c * (G * b) ≤ c * (G * (c * (q + p * G))) := mul_le_mul_of_nonneg_left this hc0.le
      _ = c ^ 2 * (G * (q + p * G)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hLn : Lr / 2 * (c * ‖s t + w t‖) ^ 2 ≤ c ^ 2 * (Lr * M ^ 2 * (1 + G ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hn2 (by positivity : 0 ≤ Lr / 2 * c ^ 2)
    calc Lr / 2 * (c * ‖s t + w t‖) ^ 2 = Lr / 2 * c ^ 2 * ‖s t + w t‖ ^ 2 := by ring
      _ ≤ Lr / 2 * c ^ 2 * (2 * M ^ 2 * (1 + G ^ 2)) := this
      _ = _ := by ring
  have hgs : c * (⟪g, s t⟫_ℝ + ⟪g, w t⟫_ℝ) ≤ -(c * (c₁ * G ^ 2)) + c * (G * b) := by
    have := mul_le_mul_of_nonneg_left (show ⟪g, s t⟫_ℝ + ⟪g, w t⟫_ℝ ≤ -(c₁ * G ^ 2) + G * b
      by linarith) hc0.le
    linarith
  have hfin : c ^ 2 * (B * G ^ 2) ≤ c * (c₁ / 2) * G ^ 2 := by
    have := mul_le_mul_of_nonneg_right hgB (by positivity : 0 ≤ c * G ^ 2)
    calc c ^ 2 * (B * G ^ 2) = c * B * (c * G ^ 2) := by ring
      _ ≤ c₁ / 2 * (c * G ^ 2) := this
      _ = _ := by ring
  have hexp : c ^ 2 * (q / 2 * (1 + G ^ 2) + p * G ^ 2) + c ^ 2 * (Lr * M ^ 2 * (1 + G ^ 2))
      = c ^ 2 * (Lr * M ^ 2 + q / 2) + c ^ 2 * (B * G ^ 2) := by rw [hB]; ring
  have hc2 : 0 ≤ c ^ 2 := by positivity
  linarith

theorem lemma_1_core (Y W Z : ℕ → ℝ) (hW : ∀ t, 0 ≤ W t)
    (hrec : ∀ t, Y (t + 1) ≤ Y t - W t + Z t)
    (hZ : ∃ S : ℝ, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), Z t) atTop (𝓝 S)) :
    Tendsto Y atTop atBot ∨ ((∃ y : ℝ, Tendsto Y atTop (𝓝 y)) ∧ Summable W) := by
  obtain ⟨S, hS⟩ := hZ
  set P : ℕ → ℝ := fun T => ∑ t ∈ Finset.range T, Z t with hP
  have hPS : Tendsto P atTop (𝓝 S) := (tendsto_add_atTop_iff_nat 1).mp hS
  set V : ℕ → ℝ := fun t => Y t - P t with hV
  have hVs : ∀ t, V (t + 1) ≤ V t - W t := by
    intro t
    simp only [hV, hP, Finset.sum_range_succ]
    linarith [hrec t]
  have hanti : Antitone V := antitone_nat_of_succ_le (fun t => by linarith [hVs t, hW t])
  have hYV : Y = fun t => V t + P t := by funext t; simp [hV]
  by_cases hb : BddBelow (Set.range V)
  · right
    obtain ⟨b, hb'⟩ := hb
    have hVb : ∀ t, b ≤ V t := fun t => hb' ⟨t, rfl⟩
    refine ⟨⟨(⨅ i, V i) + S, ?_⟩, ?_⟩
    · rw [hYV]
      exact (tendsto_atTop_ciInf hanti ⟨b, hb'⟩).add hPS
    · apply summable_of_sum_range_le hW (c := V 0 - b)
      intro N
      have : ∑ t ∈ Finset.range N, W t ≤ V 0 - V N := by
        induction N with
        | zero => simp
        | succ N ih => rw [Finset.sum_range_succ]; linarith [hVs N]
      linarith [hVb N]
  · left
    have hVbot : Tendsto V atTop atBot := by
      rw [tendsto_atTop_atBot]
      intro b
      have : ∃ N, V N < b := by
        by_contra hc
        push Not at hc
        exact hb ⟨b, by rintro _ ⟨t, rfl⟩; exact hc t⟩
      obtain ⟨N, hN⟩ := this
      exact ⟨N, fun t ht => (hanti ht).trans hN.le⟩
    rw [hYV]
    exact hVbot.atBot_add hPS


theorem sum_gamma_grad_sq_finite_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ)
    (c₁ c₂ p q : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hp : 0 < p) (hq : 0 < q)
    (hx : ∀ t, x (t + 1) = x t + γ t • (s t + w t))
    (h22a : ∀ t, c₁ * ‖gradient f (x t)‖ ^ 2 ≤ -⟪gradient f (x t), s t⟫_ℝ)
    (h22b : ∀ t, ‖s t‖ ≤ c₂ * (1 + ‖gradient f (x t)‖))
    (h23 : ∀ t, ‖w t‖ ≤ γ t * (q + p * ‖gradient f (x t)‖))
    (hγ : ∀ t, 0 < γ t)
    (hsq : Summable (fun t => γ t ^ 2)) :
    Tendsto (fun t => f (x t)) atTop atBot ∨
      ((∃ l : ℝ, Tendsto (fun t => f (x t)) atTop (𝓝 l)) ∧
        Summable (fun t => γ t * ‖gradient f (x t)‖ ^ 2)) := by
  obtain ⟨β₁, hβ₁, β₂, hβ₂, T, hT⟩ := eventual_descent_core f hf L hL x s w γ c₁ c₂ p q hc₁ hc₂
    hp hq hx h22a h22b h23 hγ hsq
  have hZs : Summable (fun t => γ (t + T) ^ 2 * β₂) :=
    ((_root_.summable_nat_add_iff T).mpr hsq).mul_right β₂
  have hrec : ∀ t, f (x (t + T + 1)) ≤ f (x (t + T))
      - γ (t + T) * β₁ * ‖gradient f (x (t + T))‖ ^ 2 + γ (t + T) ^ 2 * β₂ :=
    fun t => hT (t + T) (by omega)
  have key := lemma_1_core (fun t => f (x (t + T)))
    (fun t => γ (t + T) * β₁ * ‖gradient f (x (t + T))‖ ^ 2)
    (fun t => γ (t + T) ^ 2 * β₂) (fun t => by have := hγ (t + T); positivity)
    (fun t => by simpa [show t + 1 + T = t + T + 1 by omega] using hrec t)
    ⟨_, hZs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)⟩
  rcases key with h | ⟨⟨y, hy⟩, hW⟩
  · left
    exact (tendsto_add_atTop_iff_nat T).mp h
  · right
    refine ⟨⟨y, (tendsto_add_atTop_iff_nat T).mp hy⟩, ?_⟩
    apply (_root_.summable_nat_add_iff T).mp
    have := hW.mul_left (1 / β₁)
    refine this.congr (fun t => ?_)
    field_simp

theorem liminf_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ)
    (c₁ c₂ p q : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hp : 0 < p) (hq : 0 < q)
    (hx : ∀ t, x (t + 1) = x t + γ t • (s t + w t))
    (h22a : ∀ t, c₁ * ‖gradient f (x t)‖ ^ 2 ≤ -⟪gradient f (x t), s t⟫_ℝ)
    (h22b : ∀ t, ‖s t‖ ≤ c₂ * (1 + ‖gradient f (x t)‖))
    (h23 : ∀ t, ‖w t‖ ≤ γ t * (q + p * ‖gradient f (x t)‖))
    (hγ : ∀ t, 0 < γ t)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ¬ Tendsto (fun t => f (x t)) atTop atBot →
      ∀ ε > 0, ∃ᶠ t in atTop, ‖gradient f (x t)‖ < ε := by
  intro hnot ε hε
  rcases sum_gamma_grad_sq_finite_core f hf L hL x s w γ c₁ c₂ p q hc₁ hc₂ hp hq hx h22a h22b
    h23 hγ hsq with h | ⟨-, hS⟩
  · exact absurd h hnot
  by_contra hc
  rw [Filter.not_frequently] at hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  have hγs : Summable γ := by
    apply (_root_.summable_nat_add_iff N).mp
    refine Summable.of_nonneg_of_le (fun t => (hγ _).le) (fun t => ?_)
      (((_root_.summable_nat_add_iff N).mpr hS).div_const (ε ^ 2))
    have h1 : ε ≤ ‖gradient f (x (t + N))‖ := not_lt.mp (hN (t + N) (by omega))
    have h2 : ε ^ 2 ≤ ‖gradient f (x (t + N))‖ ^ 2 := pow_le_pow_left₀ hε.le h1 2
    rw [le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 (hγ _).le
  exact not_tendsto_atTop_of_tendsto_nhds hγs.hasSum.tendsto_sum_nat hsum

end GradErrors.Deterministic

open GradErrors.Deterministic


theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f))
    (x s w : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ)
    (c₁ c₂ p q : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hp : 0 < p) (hq : 0 < q)
    (hx : ∀ t, x (t + 1) = x t + γ t • (s t + w t))
    (h22a : ∀ t, c₁ * ‖gradient f (x t)‖ ^ 2 ≤ -⟪gradient f (x t), s t⟫_ℝ)
    (h22b : ∀ t, ‖s t‖ ≤ c₂ * (1 + ‖gradient f (x t)‖))
    (h23 : ∀ t, ‖w t‖ ≤ γ t * (q + p * ‖gradient f (x t)‖))
    (hγ : ∀ t, 0 < γ t)
    (hsum : Tendsto (fun T => ∑ t ∈ Finset.range T, γ t) atTop atTop)
    (hsq : Summable (fun t => γ t ^ 2)) :
    ¬ Tendsto (fun t => f (x t)) atTop atBot →
      ∀ ε > 0, ∃ᶠ t in atTop, ‖gradient f (x t)‖ < ε := by
  exact liminf_core f hf L hL x s w γ c₁ c₂ p q hc₁ hc₂ hp hq hx h22a h22b h23 hγ hsum hsq
