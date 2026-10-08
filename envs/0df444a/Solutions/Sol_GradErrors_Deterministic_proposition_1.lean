-- Prove2me | solution 1 for GradErrors.Deterministic.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:24:53.200987+00:00
-- url     : https://prove2.me/submissions/6913b823-0e5c-4fce-8fb4-4a8299334c65

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

/-- abstract sequence lemma -/
theorem seq_tendsto_zero (a γ : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (hγ : ∀ t, 0 < γ t)
    (hS : Summable (fun t => γ t * a t ^ 2)) (hfreq : ∀ ε > 0, ∃ᶠ t in atTop, a t < ε)
    (hγ0 : ∀ δ > 0, ∀ᶠ t in atTop, γ t ≤ δ) (K : ℝ) (hK : 0 ≤ K) (T0 : ℕ)
    (hstep : ∀ t ≥ T0, a (t + 1) ≤ a t + K * γ t * (1 + a t)) :
    Tendsto a atTop (𝓝 0) := by
  have main : ∀ ε > 0, ∀ᶠ t in atTop, a t < 2 * ε := by
    intro ε hε
    set C := K * (1 / ε ^ 2 + 1 / ε) + 1 with hC
    have hC0 : 0 < C := by positivity
    set S : ℕ → ℝ := fun m => ∑ i ∈ Finset.range m, γ i * a i ^ 2 with hSdef
    have hS0 : ∀ i, 0 ≤ γ i * a i ^ 2 := fun i => by have := hγ i; positivity
    have htail : ∀ᶠ m in atTop, (∑' i, γ i * a i ^ 2) - S m < ε / (2 * C) := by
      have := hS.hasSum.tendsto_sum_nat
      filter_upwards [this.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / (2 * C)))]
        with m hm
      rw [Real.dist_eq] at hm
      have := (abs_lt.mp hm).1
      simp only [hSdef]; linarith
    have hsmall := hγ0 (ε / (2 * (K + 1) * (1 + ε))) (by positivity)
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp (htail.and hsmall)
    obtain ⟨N, hNge, hN⟩ := frequently_atTop.mp (hfreq ε hε) (max N0 T0)
    have hNN0 : N0 ≤ N := le_trans (le_max_left _ _) hNge
    have hNT0 : T0 ≤ N := le_trans (le_max_right _ _) hNge
    have hSmono : ∀ k, S N ≤ S (N + k) := fun k =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ => hS0 i)
    have inv : ∀ k, a (N + k) ≤ 3 * ε / 2 + C * (S (N + k) - S N) := by
      intro k
      induction k with
      | zero => simp; linarith
      | succ k ih =>
        set t := N + k with ht
        have hst := hstep t (by omega)
        have hg := (hN0 t (by omega)).2
        have hSs : S (N + (k + 1)) = S t + γ t * a t ^ 2 := by
          rw [show N + (k + 1) = t + 1 by omega]; simp [hSdef, Finset.sum_range_succ]
        rw [show N + (k + 1) = t + 1 by omega] at hSs ⊢
        rw [hSs]
        have hmon := hSmono k
        have hat := ha t
        have hγt := hγ t
        rcases lt_or_ge (a t) ε with hlt | hge
        · have h1 : K * γ t * (1 + a t) ≤ K * γ t * (1 + ε) := by
            have := mul_le_mul_of_nonneg_left hlt.le (by positivity : 0 ≤ K * γ t)
            nlinarith
          have h2 : K * γ t * (1 + ε) ≤ ε / 2 := by
            have := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ (K + 1) * (1 + ε))
            have e : (K + 1) * (1 + ε) * (ε / (2 * (K + 1) * (1 + ε))) = ε / 2 := by
              field_simp
            have h3 : K * γ t * (1 + ε) ≤ (K + 1) * (1 + ε) * γ t := by
              have : 0 ≤ γ t * (1 + ε) := by positivity
              nlinarith
            linarith
          have : 0 ≤ C * (S t - S N) := mul_nonneg hC0.le (by linarith)
          have : 0 ≤ C * (γ t * a t ^ 2) := mul_nonneg hC0.le (hS0 t)
          nlinarith
        · have hr : 1 ≤ a t / ε := (one_le_div hε).mpr hge
          have hb : 1 + a t ≤ a t ^ 2 * (1 / ε ^ 2 + 1 / ε) := by
            have e : a t ^ 2 * (1 / ε ^ 2 + 1 / ε) = (a t / ε) ^ 2 + a t * (a t / ε) := by
              field_simp
            rw [e]; nlinarith
          have h1 : K * γ t * (1 + a t) ≤ C * (γ t * a t ^ 2) := by
            have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ K * γ t)
            have h4 : 0 ≤ γ t * a t ^ 2 := hS0 t
            calc K * γ t * (1 + a t) ≤ K * γ t * (a t ^ 2 * (1 / ε ^ 2 + 1 / ε)) := this
              _ = (K * (1 / ε ^ 2 + 1 / ε)) * (γ t * a t ^ 2) := by ring
              _ ≤ C * (γ t * a t ^ 2) := by
                apply mul_le_mul_of_nonneg_right _ h4; rw [hC]; linarith
          nlinarith
    filter_upwards [eventually_ge_atTop N] with t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    have h1 := inv k
    have h2 : S (N + k) ≤ ∑' i, γ i * a i ^ 2 := hS.sum_le_tsum _ (fun i _ => hS0 i)
    have h3 := (hN0 N hNN0).1
    have h4 : C * (S (N + k) - S N) < C * (ε / (2 * C)) := by
      apply mul_lt_mul_of_pos_left _ hC0; linarith
    have e : C * (ε / (2 * C)) = ε / 2 := by field_simp
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (main (ε / 3) (by positivity))
  refine ⟨N, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha t)]
  linarith [hN t ht]

theorem proposition_1_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
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
    (Tendsto (fun t => f (x t)) atTop atBot ∨
      ((∃ l : ℝ, Tendsto (fun t => f (x t)) atTop (𝓝 l)) ∧
        Tendsto (fun t => gradient f (x t)) atTop (𝓝 0))) ∧
    ∀ xbar, MapClusterPt xbar atTop x → gradient f xbar = 0 := by
  set Lr : ℝ := (L : ℝ) with hLr
  have hL0 : 0 ≤ Lr := L.2
  have hLip : ∀ a b, ‖gradient f a - gradient f b‖ ≤ Lr * ‖a - b‖ := by
    intro a b
    have := hL.dist_le_mul a b
    simpa [dist_eq_norm] using this
  have partA : Tendsto (fun t => f (x t)) atTop atBot ∨
      ((∃ l : ℝ, Tendsto (fun t => f (x t)) atTop (𝓝 l)) ∧
        Tendsto (fun t => gradient f (x t)) atTop (𝓝 0)) := by
    rcases sum_gamma_grad_sq_finite_core f hf L hL x s w γ c₁ c₂ p q hc₁ hc₂ hp hq hx h22a h22b
      h23 hγ hsq with h | ⟨⟨l, hl⟩, hS⟩
    · exact Or.inl h
    right
    refine ⟨⟨l, hl⟩, ?_⟩
    have hnot : ¬ Tendsto (fun t => f (x t)) atTop atBot := fun h =>
      not_tendsto_atBot_of_tendsto_nhds hl h
    have hfreq := liminf_core f hf L hL x s w γ c₁ c₂ p q hc₁ hc₂ hp hq hx h22a h22b h23 hγ
      hsum hsq hnot
    set M := c₂ + q + p with hM
    obtain ⟨T0, hT0⟩ := eventually_atTop.mp (ge_gamma_small γ hγ hsq 1 one_pos)
    have hstep : ∀ t ≥ T0, ‖gradient f (x (t + 1))‖ ≤ ‖gradient f (x t)‖
        + Lr * M * γ t * (1 + ‖gradient f (x t)‖) := by
      intro t ht
      have hg1 := hT0 t ht
      set G := ‖gradient f (x t)‖ with hG
      have hG0 : 0 ≤ G := norm_nonneg _
      have hc0 := hγ t
      have h1 : ‖gradient f (x (t + 1))‖ ≤ G + ‖gradient f (x (t + 1)) - gradient f (x t)‖ := by
        have := norm_le_insert' (gradient f (x (t + 1))) (gradient f (x t))
        linarith [norm_sub_rev (gradient f (x (t + 1))) (gradient f (x t))]
      have h2 := hLip (x (t + 1)) (x t)
      have hdiff : x (t + 1) - x t = γ t • (s t + w t) := by rw [hx t]; abel
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hc0] at h2
      have hsw : ‖s t + w t‖ ≤ ‖s t‖ + ‖w t‖ := norm_add_le _ _
      have hsb := h22b t
      have hwb := h23 t
      have hwb1 : ‖w t‖ ≤ q + p * G := by
        have : γ t * (q + p * G) ≤ 1 * (q + p * G) :=
          mul_le_mul_of_nonneg_right hg1 (by positivity)
        linarith
      have hab : ‖s t + w t‖ ≤ M * (1 + G) := by rw [hM]; nlinarith
      have h3 : Lr * (γ t * ‖s t + w t‖) ≤ Lr * (γ t * (M * (1 + G))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab hc0.le) hL0
      have e : Lr * (γ t * (M * (1 + G))) = Lr * M * γ t * (1 + G) := by ring
      linarith
    have ht := seq_tendsto_zero (fun t => ‖gradient f (x t)‖) γ (fun t => norm_nonneg _) hγ hS
      hfreq (fun δ hδ => ge_gamma_small γ hγ hsq δ hδ) (Lr * M) (by positivity) T0 hstep
    exact tendsto_zero_iff_norm_tendsto_zero.mpr ht
  refine ⟨partA, fun xbar hc => ?_⟩
  have hcont : Continuous f := hf.continuous
  have hgc : Continuous (gradient f) := hL.continuous
  rcases partA with h | ⟨-, hg⟩
  · exfalso
    have hfr := hc.frequently (p := fun y => f xbar - 1 < f y)
      (hcont.continuousAt.eventually (lt_mem_nhds (by linarith : f xbar - 1 < f xbar)))
    have hev := (tendsto_atTop_atBot.mp h) (f xbar - 1 - 1)
    obtain ⟨N, hN⟩ := hev
    obtain ⟨t, h1, h2⟩ := (hfr.and_eventually (eventually_ge_atTop N)).exists
    linarith [hN t h2]
  · by_contra hne
    have hpos : 0 < ‖gradient f xbar‖ := norm_pos_iff.mpr hne
    have hfr := hc.frequently (p := fun y => ‖gradient f xbar‖ / 2 < ‖gradient f y‖)
      ((hgc.norm.continuousAt).eventually (lt_mem_nhds (by linarith)))
    have hev := (tendsto_zero_iff_norm_tendsto_zero.mp hg).eventually
      (gt_mem_nhds (by positivity : (0:ℝ) < ‖gradient f xbar‖ / 2))
    obtain ⟨t, h1, h2⟩ := (hfr.and_eventually hev).exists
    linarith

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
    (Tendsto (fun t => f (x t)) atTop atBot ∨
      ((∃ l : ℝ, Tendsto (fun t => f (x t)) atTop (𝓝 l)) ∧
        Tendsto (fun t => gradient f (x t)) atTop (𝓝 0))) ∧
    ∀ xbar, MapClusterPt xbar atTop x → gradient f xbar = 0 := by
  exact proposition_1_core f hf L hL x s w γ c₁ c₂ p q hc₁ hc₂ hp hq hx h22a h22b h23 hγ hsum hsq
