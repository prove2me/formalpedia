-- Prove2me | solution 1 for NAPPAL.KL.proposition_6_1_case_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:27:25.823451+00:00
-- url     : https://prove2.me/submissions/046a10fa-054b-4e24-895f-430d153e9aec

import Mathlib
import Definitions.Def_NAPPAL_KL_Setting

open Filter Topology
open scoped InnerProductSpace


namespace NAPPALFermat
open NAPPAL.KL

lemma quad_nonneg_aux (A B τ0 : ℝ) (hτ0 : 0 < τ0)
    (h : ∀ τ : ℝ, 0 < τ → τ < τ0 → 0 ≤ τ * A + τ ^ 2 * B) : 0 ≤ A := by
  by_contra hA
  push_neg at hA
  set τ := min (τ0 / 2) ((-A) / (2 * (|B| + 1))) with hτ
  have hB1 : 0 < |B| + 1 := by positivity
  have hτpos : 0 < τ := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hτlt : τ < τ0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 := h τ hτpos hτlt
  have h2 : τ ≤ (-A) / (2 * (|B| + 1)) := min_le_right _ _
  have h3 : τ * (2 * (|B| + 1)) ≤ -A := by
    rwa [le_div_iff₀ (by positivity)] at h2
  have h4 : τ * B ≤ τ * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hτpos.le
  nlinarith

/-- One penalized step: for fixed `ε, ρ > 0` produce points `x, y` near `u` and `a`. -/
lemma fermat_step {n : ℕ} (J : E n → ℝ) (U : Set (E n)) (hUc : Convex ℝ U)
    (hUcl : IsClosed U) (u : E n) (hu : u ∈ U) (L : ℝ) (hL : 0 ≤ L) (r0 : ℝ) (hr0 : 0 < r0)
    (hlip : ∀ x ∈ Metric.closedBall u r0, ∀ y ∈ Metric.closedBall u r0,
      |J x - J y| ≤ L * ‖x - y‖)
    (v : E n) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ)
    (hv : ∀ x, dist x u < δ → x ∈ U → J u + ⟪v, x - u⟫_ℝ - ε * ‖x - u‖ ≤ J x)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ x y a : E n, ‖x - u‖ < ρ ∧ ‖y - u‖ < ρ ∧ ‖a‖ ≤ 2 * L ∧
      NonconvexSplitting.Shared.IsRegularSubgrad (fun z => (J z : EReal)) x a ∧
      ∀ z ∈ U, ⟪v - a - (2 : ℝ) • (y - u), z - y⟫_ℝ ≤ ε * ‖z - y‖ := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (min r0 δ) ρ / 2 := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; positivity
  have hrr0 : r < r0 := by
    have := min_le_left (min r0 δ) ρ; have := min_le_left r0 δ
    rw [hr]; linarith
  have hrδ : r < δ := by
    have := min_le_left (min r0 δ) ρ; have := min_le_right r0 δ
    rw [hr]; linarith
  have hrρ : r < ρ := by
    have := min_le_right (min r0 δ) ρ
    rw [hr]; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 + 2 * L / r + 4 * L ^ 2 / r ^ 2 := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : E n × E n → ℝ, Ψ = fun q => J q.1 - ⟪v, q.2 - u⟫_ℝ + ε * ‖q.2 - u‖ +
    t * ‖q.1 - q.2‖ ^ 2 + ‖q.2 - u‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Set (E n × E n), S = Metric.closedBall u r ×ˢ (U ∩ Metric.closedBall u r) :=
    ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸
    (isCompact_closedBall u r).prod ((isCompact_closedBall u r).inter_left hUcl)
  have hSne : S.Nonempty := ⟨(u, u), by
    rw [hS]; refine ⟨Metric.mem_closedBall_self hrpos.le, hu, Metric.mem_closedBall_self hrpos.le⟩⟩
  have hball : Metric.closedBall u r ⊆ Metric.closedBall u r0 :=
    Metric.closedBall_subset_closedBall hrr0.le
  have hJcont : ContinuousOn J (Metric.closedBall u r0) := by
    rw [Metric.continuousOn_iff]
    intro b hb e he
    refine ⟨e / (L + 1), by positivity, fun a ha hab => ?_⟩
    rw [Real.dist_eq]
    have := hlip a ha b hb
    rw [dist_eq_norm] at hab
    calc |J a - J b| ≤ L * ‖a - b‖ := this
      _ ≤ L * (e / (L + 1)) := mul_le_mul_of_nonneg_left hab.le hL
      _ < e := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hΨcont : ContinuousOn Ψ S := by
    rw [hΨ, hS]
    have h1 : ContinuousOn (fun q : E n × E n => J q.1)
        (Metric.closedBall u r ×ˢ (U ∩ Metric.closedBall u r)) :=
      (hJcont.mono hball).comp continuousOn_fst (fun q hq => hq.1)
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.sub h1 ?_) ?_) ?_) ?_
    · exact (continuous_const.inner (continuous_snd.sub continuous_const)).continuousOn
    · exact (continuous_const.mul (continuous_snd.sub continuous_const).norm).continuousOn
    · exact (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.pow 2)).continuousOn
    · exact (((continuous_snd.sub continuous_const).norm).pow 2).continuousOn
  obtain ⟨q, hqS, hqmin⟩ := hSc.exists_isMinOn hSne hΨcont
  obtain ⟨x, y⟩ := q
  rw [hS] at hqS
  obtain ⟨hx, hyU, hy⟩ := hqS
  simp only at hx hyU hy
  have hmin : ∀ x' y', x' ∈ Metric.closedBall u r → y' ∈ U → y' ∈ Metric.closedBall u r →
      Ψ (x, y) ≤ Ψ (x', y') := fun x' y' h1 h2 h3 => hqmin (by rw [hS]; exact ⟨h1, h2, h3⟩)
  have hxu : ‖x - u‖ ≤ r := by rw [← dist_eq_norm]; exact hx
  have hyu : ‖y - u‖ ≤ r := by rw [← dist_eq_norm]; exact hy
  -- basic estimate
  have hbase : t * ‖x - y‖ ^ 2 + ‖y - u‖ ^ 2 ≤ L * ‖x - y‖ := by
    have h1 := hmin u u (Metric.mem_closedBall_self hrpos.le) hu (Metric.mem_closedBall_self hrpos.le)
    simp only [hΨ, sub_self, inner_zero_right, norm_zero, mul_zero] at h1
    have h2 := hv y (by rw [dist_eq_norm]; linarith) hyU
    have h3 := hlip y (hball hy) x (hball hx)
    have h4 : J y - J x ≤ L * ‖x - y‖ := by
      rw [norm_sub_rev]; exact (abs_le.1 h3).2
    norm_num at h1
    linarith
  have hnxy : 0 ≤ ‖x - y‖ := norm_nonneg _
  have htxy : t * ‖x - y‖ ≤ L := by
    rcases hnxy.lt_or_eq with h | h
    · have : t * ‖x - y‖ ^ 2 ≤ L * ‖x - y‖ := by nlinarith [sq_nonneg ‖y - u‖]
      nlinarith
    · rw [← h]; simp [hL]
  have hkey1 : r / 2 * t > L := by
    rw [ht]
    have : r / 2 * (1 + 2 * L / r + 4 * L ^ 2 / r ^ 2) = r / 2 + L + 2 * L ^ 2 / r := by
      field_simp; ring
    rw [this]; have : 0 ≤ 2 * L ^ 2 / r := by positivity
    linarith
  have hkey2 : t * (r / 2) ^ 2 > L ^ 2 := by
    rw [ht]
    have : (1 + 2 * L / r + 4 * L ^ 2 / r ^ 2) * (r / 2) ^ 2 = r ^ 2 / 4 + L * r / 2 + L ^ 2 := by
      field_simp; ring
    rw [this]; have : 0 ≤ L * r / 2 := by positivity
    have : 0 < r ^ 2 / 4 := by positivity
    linarith
  have hxy_small : ‖x - y‖ < r / 2 := by
    by_contra hc; push_neg at hc
    have : r / 2 * t ≤ ‖x - y‖ * t := mul_le_mul_of_nonneg_right hc htpos.le
    linarith
  have hyu_small : ‖y - u‖ < r / 2 := by
    by_contra hc; push_neg at hc
    have h1 : (r / 2) ^ 2 ≤ ‖y - u‖ ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
    have h2 : ‖y - u‖ ^ 2 ≤ L * ‖x - y‖ := by nlinarith
    have h3 : t * (r / 2) ^ 2 ≤ t * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left (h1.trans h2) htpos.le
    have h4 : t * (L * ‖x - y‖) ≤ L * L := by nlinarith
    nlinarith
  have hxu_small : ‖x - u‖ < r := by
    calc ‖x - u‖ = ‖(x - y) + (y - u)‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y - u‖ := norm_add_le _ _
      _ < r := by linarith
  obtain ⟨a, ha⟩ : ∃ a : E n, a = (2 * t) • (y - x) := ⟨_, rfl⟩
  refine ⟨x, y, a, by linarith, by linarith, ?_, ?_, ?_⟩
  · rw [ha, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), norm_sub_rev]
    nlinarith
  · refine ⟨EReal.coe_ne_top _, fun e he => ?_⟩
    have hball' : ∀ᶠ z in 𝓝 x, dist z x < min (r - ‖x - u‖) (e / t) :=
      Metric.ball_mem_nhds x (lt_min (by linarith) (by positivity))
    filter_upwards [hball'] with z hz
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [dist_eq_norm] at hz
    have hz1 : ‖z - x‖ < r - ‖x - u‖ := lt_of_lt_of_le hz (min_le_left _ _)
    have hz2 : ‖z - x‖ < e / t := lt_of_lt_of_le hz (min_le_right _ _)
    have hzb : z ∈ Metric.closedBall u r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖z - u‖ = ‖(z - x) + (x - u)‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x - u‖ := norm_add_le _ _
        _ ≤ r := by linarith
    have h1 := hmin z y hzb hyU hy
    simp only [hΨ] at h1
    have hexp : ‖z - y‖ ^ 2 = ‖z - x‖ ^ 2 + 2 * ⟪z - x, x - y⟫_ℝ + ‖x - y‖ ^ 2 := by
      have : z - y = (z - x) + (x - y) := by abel
      rw [this, norm_add_sq_real]
    have hin : ⟪a, z - x⟫_ℝ = -(2 * t) * ⟪z - x, x - y⟫_ℝ := by
      rw [ha, real_inner_smul_left, real_inner_comm]
      have : y - x = -(x - y) := by abel
      rw [this, inner_neg_right]; ring
    have hzx : t * ‖z - x‖ ≤ e := by
      rw [lt_div_iff₀ htpos] at hz2; linarith
    have : t * ‖z - x‖ ^ 2 ≤ e * ‖z - x‖ := by
      have := mul_le_mul_of_nonneg_right hzx (norm_nonneg (z - x)); nlinarith
    rw [hin]
    have h1' : J x + t * ‖x - y‖ ^ 2 ≤ J z + t * ‖z - y‖ ^ 2 := by linarith
    rw [hexp] at h1'
    have : t * (‖z - x‖ ^ 2 + 2 * ⟪z - x, x - y⟫_ℝ + ‖x - y‖ ^ 2) =
      t * ‖z - x‖ ^ 2 + 2 * t * ⟪z - x, x - y⟫_ℝ + t * ‖x - y‖ ^ 2 := by ring
    linarith
  · intro z hz
    obtain ⟨d, hd⟩ : ∃ d : E n, d = z - y := ⟨_, rfl⟩
    have hτ0 : 0 < min 1 ((r - ‖y - u‖) / (‖d‖ + 1)) :=
      lt_min one_pos (div_pos (by linarith) (by positivity))
    have hA := quad_nonneg_aux
      (-⟪v, d⟫_ℝ + ε * ‖d‖ - 2 * t * ⟪x - y, d⟫_ℝ + 2 * ⟪y - u, d⟫_ℝ) ((t + 1) * ‖d‖ ^ 2)
      _ hτ0 (by
        intro τ hτ hτlt
        have hτ1 : τ < 1 := lt_of_lt_of_le hτlt (min_le_left _ _)
        have hτ2 : τ < (r - ‖y - u‖) / (‖d‖ + 1) := lt_of_lt_of_le hτlt (min_le_right _ _)
        have hyτU : y + τ • d ∈ U := by
          have : y + τ • d = (1 - τ) • y + τ • z := by
            rw [hd, smul_sub, sub_smul, one_smul]; abel
          rw [this]; exact hUc hyU hz (by linarith) hτ.le (by ring)
        have hyτb : y + τ • d ∈ Metric.closedBall u r := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          rw [lt_div_iff₀ (by positivity)] at hτ2
          calc ‖y + τ • d - u‖ = ‖(y - u) + τ • d‖ := by congr 1; abel
            _ ≤ ‖y - u‖ + ‖τ • d‖ := norm_add_le _ _
            _ = ‖y - u‖ + τ * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
            _ ≤ r := by nlinarith
        have h1 := hmin x (y + τ • d) hx hyτU hyτb
        simp only [hΨ] at h1
        have e1 : y + τ • d - u = (y - u) + τ • d := by abel
        have e2 : x - (y + τ • d) = (x - y) - τ • d := by abel
        rw [e1, e2] at h1
        have n1 : ‖(y - u) + τ • d‖ ≤ ‖y - u‖ + τ * ‖d‖ := by
          calc _ ≤ ‖y - u‖ + ‖τ • d‖ := norm_add_le _ _
            _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
        have n2 : ‖(y - u) + τ • d‖ ^ 2 = ‖y - u‖ ^ 2 + 2 * (τ * ⟪y - u, d⟫_ℝ) + τ ^ 2 * ‖d‖ ^ 2 := by
          rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
          ring
        have n3 : ‖(x - y) - τ • d‖ ^ 2 = ‖x - y‖ ^ 2 - 2 * (τ * ⟪x - y, d⟫_ℝ) + τ ^ 2 * ‖d‖ ^ 2 := by
          rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
          ring
        have n4 : ⟪v, (y - u) + τ • d⟫_ℝ = ⟪v, y - u⟫_ℝ + τ * ⟪v, d⟫_ℝ := by
          rw [inner_add_right, real_inner_smul_right]
        rw [n2, n3, n4] at h1
        have : ε * ‖(y - u) + τ • d‖ ≤ ε * (‖y - u‖ + τ * ‖d‖) := mul_le_mul_of_nonneg_left n1 hε.le
        have i1 : t * (‖x - y‖ ^ 2 - 2 * (τ * ⟪x - y, d⟫_ℝ) + τ ^ 2 * ‖d‖ ^ 2) =
          t * ‖x - y‖ ^ 2 - τ * (2 * t * ⟪x - y, d⟫_ℝ) + τ ^ 2 * (t * ‖d‖ ^ 2) := by ring
        have i2 : τ * (-⟪v, d⟫_ℝ + ε * ‖d‖ - 2 * t * ⟪x - y, d⟫_ℝ + 2 * ⟪y - u, d⟫_ℝ) +
            τ ^ 2 * ((t + 1) * ‖d‖ ^ 2) = -(τ * ⟪v, d⟫_ℝ) + ε * (τ * ‖d‖) -
            τ * (2 * t * ⟪x - y, d⟫_ℝ) + 2 * (τ * ⟪y - u, d⟫_ℝ) + τ ^ 2 * (t * ‖d‖ ^ 2) +
            τ ^ 2 * ‖d‖ ^ 2 := by ring
        have i3 : ε * (‖y - u‖ + τ * ‖d‖) = ε * ‖y - u‖ + ε * (τ * ‖d‖) := by ring
        rw [i2]
        linarith)
    have hin : ⟪v - a - (2 : ℝ) • (y - u), d⟫_ℝ =
        ⟪v, d⟫_ℝ + 2 * t * ⟪x - y, d⟫_ℝ - 2 * ⟪y - u, d⟫_ℝ := by
      rw [inner_sub_left, inner_sub_left, ha, real_inner_smul_left, real_inner_smul_left]
      have : y - x = -(x - y) := by abel
      rw [this, inner_neg_left]; ring
    rw [← hd, hin]; linarith

/-- Fermat rule: if `v` is a Fréchet subgradient of `J + δ_U` at `u` (with `J` Lipschitz near
`u`, `U` closed convex), then `v = a + b` with `a` a limiting subgradient of `J` and
`b ∈ N_U(u)`. -/
theorem fermat {n : ℕ} (J : E n → ℝ) (U : Set (E n)) (hUc : Convex ℝ U)
    (hUcl : IsClosed U) (u : E n) (hu : u ∈ U)
    (hJ : ∃ K : NNReal, ∃ s ∈ 𝓝 u, LipschitzOnWith K J s) (v : E n)
    (hv : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝 u, x ∈ U → J u + ⟪v, x - u⟫_ℝ - ε * ‖x - u‖ ≤ J x) :
    ∃ a ∈ NonconvexSplitting.Shared.LimitingSubdiff (fun x => (J x : EReal)) u,
      ∃ b ∈ normalCone U u, a + b = v := by
  obtain ⟨K, s, hs, hKs⟩ := hJ
  obtain ⟨r1, hr1, hr1s⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, r0 = r1 / 2 := ⟨_, rfl⟩
  have hr0pos : 0 < r0 := by rw [hr0]; positivity
  have hsub : Metric.closedBall u r0 ⊆ s :=
    (Metric.closedBall_subset_ball (by rw [hr0]; linarith)).trans hr1s
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (K : ℝ) := ⟨_, rfl⟩
  have hL : 0 ≤ L := hLdef ▸ K.2
  have hlip : ∀ x ∈ Metric.closedBall u r0, ∀ y ∈ Metric.closedBall u r0,
      |J x - J y| ≤ L * ‖x - y‖ := by
    intro x hx y hy
    have := hKs.dist_le_mul x (hsub hx) y (hsub hy)
    rwa [Real.dist_eq, dist_eq_norm, ← hLdef] at this
  have hstep : ∀ j : ℕ, ∃ x y a : E n, ‖x - u‖ < 1 / ((j : ℝ) + 1) ∧
      ‖y - u‖ < 1 / ((j : ℝ) + 1) ∧ ‖a‖ ≤ 2 * L ∧
      NonconvexSplitting.Shared.IsRegularSubgrad (fun z => (J z : EReal)) x a ∧
      ∀ z ∈ U, ⟪v - a - (2 : ℝ) • (y - u), z - y⟫_ℝ ≤ 1 / ((j : ℝ) + 1) * ‖z - y‖ := by
    intro j
    have hεj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (hv _ hεj)
    exact fermat_step J U hUc hUcl u hu L hL r0 hr0pos hlip v _ hεj δ hδ
      (fun x hx hxU => hδP hx hxU) _ hεj
  choose xs ys as hxs hys has hreg hnorm using hstep
  have hasb : ∀ j, as j ∈ Metric.closedBall (0 : E n) (2 * L) := fun j => by
    rw [mem_closedBall_zero_iff]; exact has j
  obtain ⟨a, -, φ, hφ, hφlim⟩ := tendsto_subseq_of_bounded (x := as)
    (Metric.isBounded_closedBall (x := (0 : E n)) (r := 2 * L)) hasb
  have hlim0 : Tendsto (fun i : ℕ => 1 / ((φ i : ℝ) + 1)) atTop (𝓝 0) := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  have hconv : ∀ w : ℕ → E n, (∀ j, ‖w j - u‖ < 1 / ((j : ℝ) + 1)) →
      Tendsto (fun i => w (φ i)) atTop (𝓝 u) := by
    intro w hw
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => (hw (φ i)).le) hlim0
  have hxlim := hconv xs hxs
  have hylim := hconv ys hys
  have hJc : ContinuousAt J u := by
    have : ContinuousOn J s := hKs.continuousOn
    exact this.continuousAt hs
  refine ⟨a, ⟨EReal.coe_ne_top _, fun i => xs (φ i), fun i => as (φ i), hxlim, ?_, hφlim,
    fun i => hreg (φ i)⟩, v - a, ⟨hu, fun z hz => ?_⟩, add_sub_cancel a v⟩
  · exact (continuous_coe_real_ereal.tendsto _).comp (hJc.tendsto.comp hxlim)
  · have hf : Tendsto (fun i => ⟪v - as (φ i) - (2 : ℝ) • (ys (φ i) - u), z - ys (φ i)⟫_ℝ)
        atTop (𝓝 ⟪v - a - (2 : ℝ) • (u - u), z - u⟫_ℝ) :=
      Tendsto.inner ((tendsto_const_nhds.sub hφlim).sub
        ((hylim.sub tendsto_const_nhds).const_smul _)) (tendsto_const_nhds.sub hylim)
    have hg : Tendsto (fun i => 1 / ((φ i : ℝ) + 1) * ‖z - ys (φ i)‖) atTop (𝓝 (0 * ‖z - u‖)) :=
      hlim0.mul ((tendsto_const_nhds.sub hylim).norm)
    have := le_of_tendsto_of_tendsto hf hg (Eventually.of_forall fun i => hnorm (φ i) z hz)
    simpa using this

end NAPPALFermat



namespace NAPPALAux
open NAPPAL.KL

variable {n d m : ℕ}

lemma tnorm_sq (ξ : W n d m) : tnorm ξ ^ 2 = ‖ξ.1‖ ^ 2 + ‖ξ.2.1‖ ^ 2 + ‖ξ.2.2‖ ^ 2 := by
  unfold tnorm; rw [Real.sq_sqrt (by positivity)]

lemma tnorm_nonneg (ξ : W n d m) : 0 ≤ tnorm ξ := Real.sqrt_nonneg _

lemma norm_fst_le (ξ : W n d m) : ‖ξ.1‖ ≤ tnorm ξ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (tnorm_nonneg ξ) two_ne_zero, tnorm_sq]
  nlinarith [sq_nonneg ‖ξ.2.1‖, sq_nonneg ‖ξ.2.2‖]

lemma norm_snd_fst_le (ξ : W n d m) : ‖ξ.2.1‖ ≤ tnorm ξ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (tnorm_nonneg ξ) two_ne_zero, tnorm_sq]
  nlinarith [sq_nonneg ‖ξ.1‖, sq_nonneg ‖ξ.2.2‖]

lemma norm_snd_snd_le (ξ : W n d m) : ‖ξ.2.2‖ ≤ tnorm ξ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (tnorm_nonneg ξ) two_ne_zero, tnorm_sq]
  nlinarith [sq_nonneg ‖ξ.1‖, sq_nonneg ‖ξ.2.1‖]

lemma tnorm_le_sum (ξ : W n d m) : tnorm ξ ≤ ‖ξ.1‖ + ‖ξ.2.1‖ + ‖ξ.2.2‖ := by
  rw [← pow_le_pow_iff_left₀ (tnorm_nonneg ξ) (by positivity) two_ne_zero, tnorm_sq]
  have := norm_nonneg ξ.1; have := norm_nonneg ξ.2.1; have := norm_nonneg ξ.2.2
  nlinarith [mul_nonneg (norm_nonneg ξ.1) (norm_nonneg ξ.2.1),
    mul_nonneg (norm_nonneg ξ.1) (norm_nonneg ξ.2.2),
    mul_nonneg (norm_nonneg ξ.2.1) (norm_nonneg ξ.2.2)]

lemma uv_sq_le (ξ : W n d m) : ‖ξ.1‖ ^ 2 + ‖ξ.2.1‖ ^ 2 ≤ tnorm ξ ^ 2 := by
  rw [tnorm_sq]; nlinarith [sq_nonneg ‖ξ.2.2‖]

lemma adjoint_norm_le {k l : ℕ} (A : E k →L[ℝ] E l) (x : E l) :
    ‖ContinuousLinearMap.adjoint A x‖ ≤ ‖A‖ * ‖x‖ := by
  have := (ContinuousLinearMap.adjoint A).le_opNorm x
  rwa [LinearIsometryEquiv.norm_map] at this

lemma fderiv_component (Om : E n → E m) (hOm : Differentiable ℝ Om) (u h : E n) (j : Fin m) :
    (fderiv ℝ Om u h) j = fderiv ℝ (fun x => Om x j) u h := by
  have h1 := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) j).hasFDerivAt.comp u (hOm u).hasFDerivAt
  rw [show (fun x => Om x j) = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) j) ∘ Om from rfl, h1.fderiv]
  rfl

lemma inner_gradient_eq (f : E n → ℝ) (u h : E n) : ⟪gradient f u, h⟫_ℝ = fderiv ℝ f u h := by
  unfold gradient; rw [InnerProductSpace.toDual_symm_apply]

lemma omega_diff_bound (Om : E n → E m) (hOm : Differentiable ℝ Om) (LOmj : Fin m → ℝ)
    (hL : ∀ j, 0 ≤ LOmj j ∧ ∀ u u', ‖gradient (fun x => Om x j) u -
      gradient (fun x => Om x j) u'‖ ≤ LOmj j * ‖u - u'‖)
    (u1 u0 : E n) (q : E m) :
    ‖ContinuousLinearMap.adjoint (fderiv ℝ Om u1 - fderiv ℝ Om u0) q‖ ≤
      LOm LOmj * ‖q‖ * ‖u1 - u0‖ := by
  set x := ContinuousLinearMap.adjoint (fderiv ℝ Om u1 - fderiv ℝ Om u0) q with hx
  have hLnn : 0 ≤ LOm LOmj := Finset.sum_nonneg fun j _ => (hL j).1
  have key : ∀ h : E n, ⟪x, h⟫_ℝ ≤ LOm LOmj * ‖q‖ * ‖u1 - u0‖ * ‖h‖ := by
    intro h
    rw [hx, ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
    unfold LOm
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hcomp : ((fderiv ℝ Om u1 - fderiv ℝ Om u0) h) j =
        ⟪gradient (fun x => Om x j) u1 - gradient (fun x => Om x j) u0, h⟫_ℝ := by
      rw [inner_sub_left, inner_gradient_eq, inner_gradient_eq, ContinuousLinearMap.sub_apply,
        ← fderiv_component Om hOm, ← fderiv_component Om hOm]
      rfl
    rw [hcomp]
    have h1 : |⟪gradient (fun x => Om x j) u1 - gradient (fun x => Om x j) u0, h⟫_ℝ| ≤
        LOmj j * ‖u1 - u0‖ * ‖h‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right ((hL j).2 u1 u0) (norm_nonneg _)
    have h2 : ‖q j‖ ≤ ‖q‖ := PiLp.norm_apply_le q j
    have h3 : ⟪q j, ⟪gradient (fun x => Om x j) u1 - gradient (fun x => Om x j) u0, h⟫_ℝ⟫_ℝ ≤
        ‖q j‖ * |⟪gradient (fun x => Om x j) u1 - gradient (fun x => Om x j) u0, h⟫_ℝ| := by
      have := real_inner_le_norm (q j)
        (⟪gradient (fun x => Om x j) u1 - gradient (fun x => Om x j) u0, h⟫_ℝ)
      simpa [Real.norm_eq_abs] using this
    have h4 : 0 ≤ LOmj j * ‖u1 - u0‖ * ‖h‖ := by
      have := (hL j).1; positivity
    calc _ ≤ ‖q j‖ * |⟪gradient (fun x => Om x j) u1 - gradient (fun x => Om x j) u0, h⟫_ℝ| := h3
      _ ≤ ‖q‖ * (LOmj j * ‖u1 - u0‖ * ‖h‖) :=
          mul_le_mul h2 h1 (abs_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hxx := key x
  rw [real_inner_self_eq_norm_sq] at hxx
  rcases (norm_nonneg x).lt_or_eq with hpos | hzero
  · have : ‖x‖ * ‖x‖ ≤ (LOm LOmj * ‖q‖ * ‖u1 - u0‖) * ‖x‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

end NAPPALAux



namespace NAPPALMain
open NAPPAL.KL NAPPALAux

variable {n d m : ℕ}

/-- First-order optimality of the `v`-subproblem (6). -/
lemma v_opt (B : E d →L[ℝ] E m) (γ : ℝ) (hγ : 0 < γ) (c : E d) (q : E m) (v0 v1 : E d)
    (h6 : ∀ v' : E d, ⟪c, v1⟫_ℝ + ⟪q, B v1⟫_ℝ + γ / 2 * ‖B (v1 - v0)‖ ^ 2 ≤
        ⟪c, v'⟫_ℝ + ⟪q, B v'⟫_ℝ + γ / 2 * ‖B (v' - v0)‖ ^ 2) :
    c + ContinuousLinearMap.adjoint B q + γ • ContinuousLinearMap.adjoint B (B (v1 - v0)) = 0 := by
  obtain ⟨G, hG⟩ : ∃ G : E d, G = c + ContinuousLinearMap.adjoint B q +
      γ • ContinuousLinearMap.adjoint B (B (v1 - v0)) := ⟨_, rfl⟩
  rw [← hG]
  have hGG : ‖G‖ ^ 2 = ⟪c, G⟫_ℝ + ⟪q, B G⟫_ℝ + γ * ⟪B (v1 - v0), B G⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [hG]
    rw [inner_add_left, inner_add_left, real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  have hA := NAPPALFermat.quad_nonneg_aux (-‖G‖ ^ 2) (γ / 2 * ‖B G‖ ^ 2) 1 one_pos (by
    intro τ hτ _
    have h := h6 (v1 - τ • G)
    have e2 : B (v1 - τ • G - v0) = B (v1 - v0) - τ • B G := by
      rw [show v1 - τ • G - v0 = (v1 - v0) - τ • G by abel, map_sub, map_smul]
    have e3 : B (v1 - τ • G) = B v1 - τ • B G := by rw [map_sub, map_smul]
    rw [e2, e3, inner_sub_right, inner_sub_right,
      real_inner_smul_right, real_inner_smul_right, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hτ] at h
    rw [hGG]
    nlinarith)
  have : ‖G‖ ^ 2 ≤ 0 := by linarith
  have : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
  exact norm_eq_zero.1 this

/-- The Fréchet-subgradient inequality coming from the `u`-subproblem (5). -/
lemma u_frechet (J : E n → ℝ) (U : Set (E n)) (gU : E n) (q : E m) (A : E n →L[ℝ] E m)
    (Φ : E n → E m) (hΦ : Differentiable ℝ Φ) (K : E n → ℝ) (hK : Differentiable ℝ K)
    (ε : ℝ) (hε : 0 < ε) (u0 u1 : E n)
    (h5 : ∀ u' ∈ U, ⟪gU, u1⟫_ℝ + J u1 + ⟪q, A u1 + Φ u1⟫_ℝ + bregman K u1 u0 / ε ≤
      ⟪gU, u'⟫_ℝ + J u' + ⟪q, A u' + Φ u'⟫_ℝ + bregman K u' u0 / ε) :
    ∀ e : ℝ, 0 < e → ∀ᶠ x in 𝓝 u1, x ∈ U →
      J u1 + ⟪-(gU + ContinuousLinearMap.adjoint A q +
        ContinuousLinearMap.adjoint (fderiv ℝ Φ u1) q +
        ε⁻¹ • (gradient K u1 - gradient K u0)), x - u1⟫_ℝ - e * ‖x - u1‖ ≤ J x := by
  intro e he
  have hΦo := (hΦ u1).hasFDerivAt.isLittleO
  have hKo := (hK u1).hasFDerivAt.isLittleO
  have c1pos : 0 < e / (2 * (‖q‖ + 1)) := by positivity
  have c2pos : 0 < e * ε / 2 := by positivity
  filter_upwards [hΦo.def c1pos, hKo.def c2pos] with x hx1 hx2 hxU
  have h := h5 x hxU
  have i1 : ⟪-(gU + ContinuousLinearMap.adjoint A q +
        ContinuousLinearMap.adjoint (fderiv ℝ Φ u1) q +
        ε⁻¹ • (gradient K u1 - gradient K u0)), x - u1⟫_ℝ =
      -(⟪gU, x - u1⟫_ℝ + ⟪q, A (x - u1)⟫_ℝ + ⟪q, fderiv ℝ Φ u1 (x - u1)⟫_ℝ +
        ε⁻¹ * (fderiv ℝ K u1 (x - u1) - ⟪gradient K u0, x - u1⟫_ℝ)) := by
    rw [inner_neg_left, inner_add_left, inner_add_left, inner_add_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      real_inner_smul_left, inner_sub_left, inner_gradient_eq]
  have i2 : ⟪q, A x + Φ x⟫_ℝ - ⟪q, A u1 + Φ u1⟫_ℝ = ⟪q, A (x - u1)⟫_ℝ +
      ⟪q, fderiv ℝ Φ u1 (x - u1)⟫_ℝ + ⟪q, Φ x - Φ u1 - fderiv ℝ Φ u1 (x - u1)⟫_ℝ := by
    simp only [map_sub, inner_add_right, inner_sub_right]; ring
  have i3 : bregman K x u0 / ε - bregman K u1 u0 / ε =
      ε⁻¹ * (fderiv ℝ K u1 (x - u1) - ⟪gradient K u0, x - u1⟫_ℝ) +
        (K x - K u1 - fderiv ℝ K u1 (x - u1)) / ε := by
    simp only [bregman, inner_sub_right]; field_simp; ring
  have i4 : ⟪gU, x⟫_ℝ - ⟪gU, u1⟫_ℝ = ⟪gU, x - u1⟫_ℝ := by rw [inner_sub_right]
  have b1 : ⟪q, Φ x - Φ u1 - fderiv ℝ Φ u1 (x - u1)⟫_ℝ ≤ e / 2 * ‖x - u1‖ := by
    refine (real_inner_le_norm _ _).trans ?_
    calc ‖q‖ * ‖Φ x - Φ u1 - fderiv ℝ Φ u1 (x - u1)‖
        ≤ ‖q‖ * (e / (2 * (‖q‖ + 1)) * ‖x - u1‖) :=
          mul_le_mul_of_nonneg_left hx1 (norm_nonneg _)
      _ = (e / 2) * (‖q‖ / (‖q‖ + 1)) * ‖x - u1‖ := by field_simp
      _ ≤ (e / 2) * 1 * ‖x - u1‖ := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = _ := by ring
  have b2 : (K x - K u1 - fderiv ℝ K u1 (x - u1)) / ε ≤ e / 2 * ‖x - u1‖ := by
    rw [div_le_iff₀ hε]
    have := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hx2)
    nlinarith
  rw [i1]
  linarith

lemma jac_eq (P : Problem n d m) (hOm : Differentiable ℝ P.Om) (hPhi : Differentiable ℝ P.Phi)
    (u : E n) : jac P u = fderiv ℝ P.Om u + fderiv ℝ P.Phi u := by
  unfold jac
  exact fderiv_add (hOm u) (hPhi u)

/-- `q^k = p^k + γ (Θ(u^k) + B v^k)`. -/
noncomputable def qv (P : Problem n d m) (γ : ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (k : ℕ) : E m :=
  p k + γ • (Theta P (u k) + P.B (v k))

/-- The `k`-independent part of the constant in Theorem 4.1(iv). -/
noncomputable def A0 (P : Problem n d m) (LG LH L0 γ : ℝ) : ℝ :=
  2 * LG + LH + (L0 + ‖P.B‖) * (1 + γ * (L0 + ‖P.B‖)) + γ * ‖P.B‖ ^ 2 + 1 / γ

/-- Theorem 4.1(iv) of the paper, in a form with explicit (k-dependent) constant:
an element of `∂L_γ(w^{k+1})` bounded by a multiple of `‖w^k - w^{k+1}‖`. -/
theorem subgrad_bound (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d)
    (p : ℕ → E m) (hrun : RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p) (k : ℕ) :
    ∃ ξ ∈ dAugLag P γ (wseq u v p (k + 1)),
      tnorm ξ ≤ (A0 P LG LH L0 γ + LOm LOmj * ‖qv P γ u v p k‖ + LK * (ε k)⁻¹) *
        wdist (wseq u v p k) (wseq u v p (k + 1)) := by
  obtain ⟨hA1, hA2, hN, -⟩ := hrun
  obtain ⟨⟨-, hLG, hGlip⟩, ⟨-, hLH, hHlip⟩, ⟨-, hJlip, hUc, hUcl⟩,
    ⟨hOmd, hPhid, hL0, hTlip⟩, hOmL, -, -⟩ := hA1
  obtain ⟨hKd, -, -, hLK, hKlip, -⟩ := hA2
  obtain ⟨hγ, hσ, -, hk⟩ := hN
  obtain ⟨hδk, hσδ, -, ⟨hu1U, h5⟩, h6, h7⟩ := hk k
  have hεpos : 0 < ε k := lt_of_lt_of_le (mul_pos hσ hδk) hσδ
  have hLOm : 0 ≤ LOm LOmj := Finset.sum_nonneg fun j _ => (hOmL j).1
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = wdist (wseq u v p k) (wseq u v p (k + 1)) := ⟨_, rfl⟩
  rw [← hΔ]
  have hΔnn : 0 ≤ Δ := hΔ ▸ tnorm_nonneg _
  have hΔu : ‖u (k + 1) - u k‖ ≤ Δ := by
    rw [norm_sub_rev, hΔ]; exact norm_fst_le (wseq u v p k - wseq u v p (k + 1))
  have hΔv : ‖v (k + 1) - v k‖ ≤ Δ := by
    rw [norm_sub_rev, hΔ]; exact norm_snd_fst_le (wseq u v p k - wseq u v p (k + 1))
  have hΔp : ‖p (k + 1) - p k‖ ≤ Δ := by
    rw [norm_sub_rev, hΔ]; exact norm_snd_snd_le (wseq u v p k - wseq u v p (k + 1))
  have hΔuv : ‖u (k + 1) - u k‖ ^ 2 + ‖v (k + 1) - v k‖ ^ 2 ≤ Δ ^ 2 := by
    rw [norm_sub_rev, norm_sub_rev (v (k + 1)), hΔ]
    exact uv_sq_le (wseq u v p k - wseq u v p (k + 1))
  obtain ⟨q, hq⟩ : ∃ q, q = qv P γ u v p k := ⟨_, rfl⟩
  rw [← hq]
  have hq' : p k + γ • (Theta P (u k) + P.B (v k)) = q := by rw [hq]; rfl
  rw [hq'] at h5 h6
  -- optimality conditions
  have hGv := v_opt P.B γ hγ (gradV P (u k) (v k) + gradient P.H (v k)) q (v k) (v (k + 1)) h6
  have hv := u_frechet P.J P.U (gradU P (u k) (v k)) q (fderiv ℝ P.Om (u k)) P.Phi hPhid K hKd
    (ε k) hεpos (u k) (u (k + 1)) h5
  obtain ⟨a, ha, b, hb, hab⟩ :=
    NAPPALFermat.fermat P.J P.U hUc hUcl (u (k + 1)) hu1U (hJlip _ hu1U) _ hv
  obtain ⟨y, hy⟩ : ∃ y, y = p (k + 1) + γ • (Theta P (u (k + 1)) + P.B (v (k + 1))) := ⟨_, rfl⟩
  refine ⟨(gradU P (u (k + 1)) (v (k + 1)) + a + b +
      ContinuousLinearMap.adjoint (jac P (u (k + 1))) y,
    gradV P (u (k + 1)) (v (k + 1)) + gradient P.H (v (k + 1)) +
      ContinuousLinearMap.adjoint P.B y,
    Theta P (u (k + 1)) + P.B (v (k + 1))), ⟨a, ha, b, hb, by rw [hy]; rfl, by rw [hy]; rfl, rfl⟩,
    ?_⟩
  refine (tnorm_le_sum _).trans ?_
  dsimp only
  -- common estimates
  have hyq : y - q = (p (k + 1) - p k) +
      γ • ((Theta P (u (k + 1)) - Theta P (u k)) + P.B (v (k + 1) - v k)) := by
    rw [hy, hq]; simp only [qv, map_sub, smul_add, smul_sub]; abel
  have hr : ‖(Theta P (u (k + 1)) - Theta P (u k)) + P.B (v (k + 1) - v k)‖ ≤
      (L0 + ‖P.B‖) * Δ := by
    refine (norm_add_le _ _).trans ?_
    have h1 := (hTlip (u (k + 1)) (u k)).trans (mul_le_mul_of_nonneg_left hΔu hL0)
    have h2 := (P.B.le_opNorm (v (k + 1) - v k)).trans
      (mul_le_mul_of_nonneg_left hΔv (norm_nonneg _))
    linarith
  set c := 1 + γ * (L0 + ‖P.B‖) with hc
  have hyqn : ‖y - q‖ ≤ c * Δ := by
    rw [hyq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    have := mul_le_mul_of_nonneg_left hr hγ.le
    rw [hc]; nlinarith
  have hgrad := hGlip (u (k + 1)) (v (k + 1)) (u k) (v k)
  have hgU : ‖gradU P (u (k + 1)) (v (k + 1)) - gradU P (u k) (v k)‖ ≤ LG * Δ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero]
    have := mul_le_mul_of_nonneg_left hΔuv (sq_nonneg LG)
    nlinarith [sq_nonneg ‖gradV P (u (k + 1)) (v (k + 1)) - gradV P (u k) (v k)‖]
  have hgV : ‖gradV P (u (k + 1)) (v (k + 1)) - gradV P (u k) (v k)‖ ≤ LG * Δ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero]
    have := mul_le_mul_of_nonneg_left hΔuv (sq_nonneg LG)
    nlinarith [sq_nonneg ‖gradU P (u (k + 1)) (v (k + 1)) - gradU P (u k) (v k)‖]
  -- first block
  have hx1 : gradU P (u (k + 1)) (v (k + 1)) + a + b +
      ContinuousLinearMap.adjoint (jac P (u (k + 1))) y =
      (gradU P (u (k + 1)) (v (k + 1)) - gradU P (u k) (v k)) +
      ContinuousLinearMap.adjoint (fderiv ℝ P.Om (u (k + 1)) - fderiv ℝ P.Om (u k)) q +
      ContinuousLinearMap.adjoint (jac P (u (k + 1))) (y - q) -
      (ε k)⁻¹ • (gradient K (u (k + 1)) - gradient K (u k)) := by
    rw [add_assoc (gradU P (u (k + 1)) (v (k + 1))) a b, hab, jac_eq P hOmd hPhid]
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    abel
  have hjacn : ‖jac P (u (k + 1))‖ ≤ L0 := by
    unfold jac
    exact norm_fderiv_le_of_lip' ℝ hL0 (Eventually.of_forall fun x => hTlip x _)
  have hn1 : ‖gradU P (u (k + 1)) (v (k + 1)) + a + b +
      ContinuousLinearMap.adjoint (jac P (u (k + 1))) y‖ ≤
      LG * Δ + LOm LOmj * ‖q‖ * Δ + L0 * (c * Δ) + (ε k)⁻¹ * (LK * Δ) := by
    rw [hx1]
    refine (norm_sub_le _ _).trans ?_
    have t1 := norm_add₃_le (a := gradU P (u (k + 1)) (v (k + 1)) - gradU P (u k) (v k))
      (b := ContinuousLinearMap.adjoint (fderiv ℝ P.Om (u (k + 1)) - fderiv ℝ P.Om (u k)) q)
      (c := ContinuousLinearMap.adjoint (jac P (u (k + 1))) (y - q))
    have t2 := NAPPALAux.omega_diff_bound P.Om hOmd LOmj hOmL (u (k + 1)) (u k) q
    have t2' : LOm LOmj * ‖q‖ * ‖u (k + 1) - u k‖ ≤ LOm LOmj * ‖q‖ * Δ :=
      mul_le_mul_of_nonneg_left hΔu (by positivity)
    have t3 := NAPPALAux.adjoint_norm_le (jac P (u (k + 1))) (y - q)
    have t3' : ‖jac P (u (k + 1))‖ * ‖y - q‖ ≤ L0 * (c * Δ) :=
      mul_le_mul hjacn hyqn (norm_nonneg _) hL0
    have t4 : ‖(ε k)⁻¹ • (gradient K (u (k + 1)) - gradient K (u k))‖ ≤ (ε k)⁻¹ * (LK * Δ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hεpos)]
      exact mul_le_mul_of_nonneg_left ((hKlip _ _).trans (mul_le_mul_of_nonneg_left hΔu hLK))
        (inv_pos.2 hεpos).le
    linarith
  -- second block
  have hx2 : gradV P (u (k + 1)) (v (k + 1)) + gradient P.H (v (k + 1)) +
      ContinuousLinearMap.adjoint P.B y =
      (gradV P (u (k + 1)) (v (k + 1)) - gradV P (u k) (v k)) +
      (gradient P.H (v (k + 1)) - gradient P.H (v k)) +
      ContinuousLinearMap.adjoint P.B (y - q) -
      γ • ContinuousLinearMap.adjoint P.B (P.B (v (k + 1) - v k)) := by
    have e : ContinuousLinearMap.adjoint P.B (y - q) =
        ContinuousLinearMap.adjoint P.B y - ContinuousLinearMap.adjoint P.B q := map_sub _ _ _
    rw [e]
    have := congrArg (fun z => gradV P (u (k + 1)) (v (k + 1)) + gradient P.H (v (k + 1)) +
      ContinuousLinearMap.adjoint P.B y - z) hGv
    simp only [sub_zero] at this
    rw [← this]
    abel
  have hn2 : ‖gradV P (u (k + 1)) (v (k + 1)) + gradient P.H (v (k + 1)) +
      ContinuousLinearMap.adjoint P.B y‖ ≤
      LG * Δ + LH * Δ + ‖P.B‖ * (c * Δ) + γ * (‖P.B‖ * (‖P.B‖ * Δ)) := by
    rw [hx2]
    refine (norm_sub_le _ _).trans ?_
    have t1 := norm_add₃_le (a := gradV P (u (k + 1)) (v (k + 1)) - gradV P (u k) (v k))
      (b := gradient P.H (v (k + 1)) - gradient P.H (v k))
      (c := ContinuousLinearMap.adjoint P.B (y - q))
    have t2 := (hHlip (v (k + 1)) (v k)).trans (mul_le_mul_of_nonneg_left hΔv hLH)
    have t3 := (NAPPALAux.adjoint_norm_le P.B (y - q)).trans
      (mul_le_mul_of_nonneg_left hyqn (norm_nonneg _))
    have t4 : ‖γ • ContinuousLinearMap.adjoint P.B (P.B (v (k + 1) - v k))‖ ≤
        γ * (‖P.B‖ * (‖P.B‖ * Δ)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      refine mul_le_mul_of_nonneg_left ?_ hγ.le
      refine (NAPPALAux.adjoint_norm_le P.B _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (P.B.le_opNorm _).trans (mul_le_mul_of_nonneg_left hΔv (norm_nonneg _))
    linarith
  -- third block
  have hx3 : Theta P (u (k + 1)) + P.B (v (k + 1)) = γ⁻¹ • (p (k + 1) - p k) := by
    rw [h7, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  have hn3 : ‖Theta P (u (k + 1)) + P.B (v (k + 1))‖ ≤ γ⁻¹ * Δ := by
    rw [hx3, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hγ)]
    exact mul_le_mul_of_nonneg_left hΔp (inv_pos.2 hγ).le
  have hsum : (A0 P LG LH L0 γ + LOm LOmj * ‖q‖ + LK * (ε k)⁻¹) * Δ =
      (LG * Δ + LOm LOmj * ‖q‖ * Δ + L0 * (c * Δ) + (ε k)⁻¹ * (LK * Δ)) +
      (LG * Δ + LH * Δ + ‖P.B‖ * (c * Δ) + γ * (‖P.B‖ * (‖P.B‖ * Δ))) + γ⁻¹ * Δ := by
    rw [hc]; unfold A0; ring
  rw [hsum]
  linarith

theorem case1 {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ)
    (LOmj : Fin m → ℝ) (LK : ℝ) (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n)
    (v : ℕ → E d) (p : ℕ → E m) (hrun : RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p)
    (wbar : W n d m) (η ν κ2 : ℝ)
    (hKL : HasKLAt P γ wbar (1 / 2) η ν κ2) :
    ∃ c5 : ℝ, 0 < c5 ∧ ∀ k : ℕ, wdist (wseq u v p (k + 1)) wbar < η →
      augLag P γ wbar < augLag P γ (wseq u v p (k + 1)) →
      augLag P γ (wseq u v p (k + 1)) < augLag P γ wbar + ν →
      ENNReal.ofReal (augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar) ≤
          (ENNReal.ofReal κ2 * distZero (dAugLag P γ (wseq u v p (k + 1)))) ^ 2 ∧
        augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar ≤
          (κ2 * c5) ^ 2 * wdist (wseq u v p k) (wseq u v p (k + 1)) ^ 2 := by
  obtain ⟨-, -, hη, hν, hκ2, hKLi⟩ := hKL
  have hrun' := hrun
  obtain ⟨hA1, hA2, hN, hδ⟩ := hrun'
  obtain ⟨⟨-, hLG, -⟩, ⟨-, hLH, -⟩, -, ⟨-, -, hL0, hTlip⟩, hOmL, ⟨-, hlam⟩, -⟩ := hA1
  obtain ⟨-, hβ, -, hLK, -, -⟩ := hA2
  obtain ⟨hγ, hσ, -, hk⟩ := hN
  have hLOm : 0 ≤ LOm LOmj := Finset.sum_nonneg fun j _ => (hOmL j).1
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ‖wbar.2.2‖ + η + γ * (L0 + ‖P.B‖) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = LG + Q * LOm LOmj + γ * L0 ^ 2 +
      14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
      14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = A0 P LG LH L0 γ + LOm LOmj * Q + LK * (D / (σ * β)) :=
    ⟨_, rfl⟩
  obtain ⟨c5, hc5⟩ : ∃ c5 : ℝ, c5 = max C 0 + Real.sqrt ν / κ2 + 1 := ⟨_, rfl⟩
  have hc5pos : 0 < c5 := by
    rw [hc5]; have := le_max_right C 0; have : 0 ≤ Real.sqrt ν / κ2 := by positivity
    linarith
  refine ⟨c5, hc5pos, fun k hd hlo hhi => ?_⟩
  have hx : 0 < augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar := by linarith
  have hKLk := hKLi _ hd hlo hhi
  have hsq : ENNReal.ofReal ((augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar) ^ (1 / 2 : ℝ))
      ^ 2 = ENNReal.ofReal (augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
  refine ⟨by rw [← hsq]; exact pow_le_pow_left₀ (zero_le) hKLk 2, ?_⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = wdist (wseq u v p k) (wseq u v p (k + 1)) := ⟨_, rfl⟩
  rw [← hΔ]
  have hΔnn : 0 ≤ Δ := hΔ ▸ tnorm_nonneg _
  by_cases hbig : 1 ≤ Δ
  · have h0 : Real.sqrt ν / κ2 ≤ c5 := by
      rw [hc5]; have := le_max_right C 0; linarith
    have h1 : Real.sqrt ν ≤ κ2 * c5 := by
      rw [div_le_iff₀ hκ2] at h0; linarith
    have h2 : ν ≤ (κ2 * c5) ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rwa [Real.sq_sqrt hν.le] at this
    have h3 : (κ2 * c5) ^ 2 ≤ (κ2 * c5) ^ 2 * Δ ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hbig)
    linarith
  · push_neg at hbig
    obtain ⟨ξ, hξ, hξn⟩ := subgrad_bound P LG LH L0 LOmj LK K β γ σ δ ε u v p hrun k
    rw [← hΔ] at hξn
    obtain ⟨hδk, hσδ, -, -, -, h7⟩ := hk k
    -- bound on q^k
    have hqeq : qv P γ u v p k = p (k + 1) +
        γ • ((Theta P (u k) - Theta P (u (k + 1))) + P.B (v k - v (k + 1))) := by
      unfold qv; rw [h7]; simp only [map_sub, smul_add, smul_sub]; abel
    have hp1 : ‖p (k + 1)‖ ≤ ‖wbar.2.2‖ + η := by
      have h1 : ‖p (k + 1) - wbar.2.2‖ ≤ wdist (wseq u v p (k + 1)) wbar :=
        norm_snd_snd_le (wseq u v p (k + 1) - wbar)
      have h2 := norm_le_insert' (p (k + 1)) wbar.2.2
      linarith
    have hΔu : ‖u k - u (k + 1)‖ ≤ Δ := hΔ ▸ norm_fst_le (wseq u v p k - wseq u v p (k + 1))
    have hΔv : ‖v k - v (k + 1)‖ ≤ Δ := hΔ ▸ norm_snd_fst_le (wseq u v p k - wseq u v p (k + 1))
    have hr : ‖(Theta P (u k) - Theta P (u (k + 1))) + P.B (v k - v (k + 1))‖ ≤ L0 + ‖P.B‖ := by
      refine (norm_add_le _ _).trans ?_
      have h1 := (hTlip (u k) (u (k + 1))).trans (mul_le_mul_of_nonneg_left hΔu hL0)
      have h2 := (P.B.le_opNorm (v k - v (k + 1))).trans
        (mul_le_mul_of_nonneg_left hΔv (norm_nonneg _))
      have h3 : L0 * Δ ≤ L0 := by nlinarith
      have h4 : ‖P.B‖ * Δ ≤ ‖P.B‖ := by nlinarith [norm_nonneg P.B]
      linarith
    have hq : ‖qv P γ u v p k‖ ≤ Q := by
      rw [hqeq, hQ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      have := mul_le_mul_of_nonneg_left hr hγ.le
      linarith
    -- bound on 1/ε_k
    have hDq : δ k = β / (LG + ‖qv P γ u v p k‖ * LOm LOmj + γ * L0 ^ 2 +
        14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
        14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) + 1) := by
      rw [hδ k]; rfl
    have hDqpos : 0 < LG + ‖qv P γ u v p k‖ * LOm LOmj + γ * L0 ^ 2 +
        14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
        14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) + 1 := by positivity
    have hDle : LG + ‖qv P γ u v p k‖ * LOm LOmj + γ * L0 ^ 2 +
        14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
        14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) + 1 ≤ D := by
      rw [hD]; have := mul_le_mul_of_nonneg_right hq hLOm; linarith
    have hεinv : (ε k)⁻¹ ≤ D / (σ * β) := by
      have hσδpos : 0 < σ * δ k := mul_pos hσ hδk
      refine (inv_anti₀ hσδpos hσδ).trans ?_
      rw [hDq, mul_div_assoc', inv_div]
      exact div_le_div_of_nonneg_right hDle (by positivity)
    have hCle : A0 P LG LH L0 γ + LOm LOmj * ‖qv P γ u v p k‖ + LK * (ε k)⁻¹ ≤ c5 := by
      have h1 := mul_le_mul_of_nonneg_left hq hLOm
      have h2 := mul_le_mul_of_nonneg_left hεinv hLK
      have : C ≤ max C 0 := le_max_left _ _
      have : 0 ≤ Real.sqrt ν / κ2 := by positivity
      rw [hc5]; rw [hC] at *; linarith
    have hξ' : tnorm ξ ≤ c5 * Δ := hξn.trans (mul_le_mul_of_nonneg_right hCle hΔnn)
    have hdist : distZero (dAugLag P γ (wseq u v p (k + 1))) ≤ ENNReal.ofReal (tnorm ξ) :=
      iInf₂_le ξ hξ
    have hchain : ENNReal.ofReal ((augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar) ^
        (1 / 2 : ℝ)) ≤ ENNReal.ofReal (κ2 * (c5 * Δ)) := by
      refine hKLk.trans ?_
      rw [ENNReal.ofReal_mul hκ2.le]
      gcongr
      exact hdist.trans (ENNReal.ofReal_le_ofReal hξ')
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
    have h2 := pow_le_pow_left₀ (by positivity) h 2
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le] at h2
    calc _ ≤ (κ2 * (c5 * Δ)) ^ 2 := h2
      _ = _ := by ring

end NAPPALMain

open NAPPAL.KL in
theorem solution {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ)
    (LOmj : Fin m → ℝ) (LK : ℝ) (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n)
    (v : ℕ → E d) (p : ℕ → E m) (hrun : RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p)
    (wbar : W n d m) (hcl : MapClusterPt wbar Filter.atTop (wseq u v p)) (η ν κ2 : ℝ)
    (hKL : HasKLAt P γ wbar (1 / 2) η ν κ2) :
    ∃ c5 : ℝ, 0 < c5 ∧ ∀ k : ℕ, wdist (wseq u v p (k + 1)) wbar < η →
      augLag P γ wbar < augLag P γ (wseq u v p (k + 1)) →
      augLag P γ (wseq u v p (k + 1)) < augLag P γ wbar + ν →
      ENNReal.ofReal (augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar) ≤
          (ENNReal.ofReal κ2 * distZero (dAugLag P γ (wseq u v p (k + 1)))) ^ 2 ∧
        augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar ≤
          (κ2 * c5) ^ 2 * wdist (wseq u v p k) (wseq u v p (k + 1)) ^ 2 :=
  NAPPALMain.case1 P LG LH L0 LOmj LK K β γ σ δ ε u v p hrun wbar η ν κ2 hKL
