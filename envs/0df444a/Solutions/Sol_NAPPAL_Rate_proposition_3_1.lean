-- Prove2me | solution 1 for NAPPAL.Rate.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:10:13.629038+00:00
-- url     : https://prove2.me/submissions/291d9d44-a0de-45fc-8c1d-8a855030af84

import Mathlib
import Definitions.Def_NAPPAL_Rate_Setting
open Filter Topology
open scoped InnerProductSpace
open NAPPAL.KL NAPPAL.Rate

namespace NAPPALP31

open NonconvexSplitting.Shared

/-- A quadratic lower model on a ball gives a regular subgradient. -/
theorem regular_of_quad {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (J : X → ℝ) (z0 a : X) (ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (h : ∀ z, ‖z - z0‖ < ρ → J z0 + ⟪a, z - z0⟫_ℝ - M * ‖z - z0‖ ^ 2 ≤ J z) :
    IsRegularSubgrad (fun x => (J x : EReal)) z0 a := by
  refine ⟨EReal.coe_ne_top _, fun ε hε => ?_⟩
  have hr : 0 < min ρ (ε / (M + 1)) := lt_min hρ (by positivity)
  filter_upwards [Metric.ball_mem_nhds z0 hr] with z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := h z (lt_of_lt_of_le hz (min_le_left _ _))
  have h2 : ‖z - z0‖ < ε / (M + 1) := lt_of_lt_of_le hz (min_le_right _ _)
  have h3 : M * ‖z - z0‖ ^ 2 ≤ ε * ‖z - z0‖ := by
    have hn := norm_nonneg (z - z0)
    have : (M + 1) * ‖z - z0‖ ≤ ε := by
      rw [lt_div_iff₀ (by positivity)] at h2; linarith
    nlinarith
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- If `X ≤ c + λ e` for all small `λ > 0`, then `X ≤ c`. -/
theorem le_of_small (X c e l0 : ℝ) (hl0 : 0 < l0) (he : 0 ≤ e)
    (h : ∀ l, 0 < l → l ≤ l0 → X ≤ c + l * e) : X ≤ c := by
  by_contra hX
  rw [not_le] at hX
  set l := min l0 ((X - c) / (2 * (e + 1))) with hl
  have hlpos : 0 < l := lt_min hl0 (by apply div_pos <;> linarith)
  have h1 := h l hlpos (min_le_left _ _)
  have h2 : l ≤ (X - c) / (2 * (e + 1)) := min_le_right _ _
  rw [le_div_iff₀ (by linarith)] at h2
  nlinarith

set_option maxHeartbeats 2000000 in
/-- One penalized step of the decoupling argument. -/
theorem step {n : ℕ} (J : E n → ℝ) (hJ : LowerSemicontinuous J) (U : Set (E n))
    (hU : Convex ℝ U) (hUc : IsClosed U) (x : E n) (hx : x ∈ U) (v : E n)
    (K : NNReal) (t : Set (E n)) (hK : LipschitzOnWith K J t)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hε : 0 < ε) (hball : Metric.closedBall x ρ ⊆ t)
    (hmin : ∀ y ∈ U, ‖y - x‖ ≤ ρ → J x - ⟪v, x⟫_ℝ ≤ J y - ⟪v, y⟫_ℝ + ε * ‖y - x‖) :
    ∃ z y a bb : E n, ‖z - x‖ < ρ ∧ ‖y - x‖ < ρ ∧ IsRegularSubgrad (fun x => (J x : EReal)) z a ∧
      v = a + bb + (2 : ℝ) • (z - x) ∧ ‖bb‖ ≤ 2 * ((K : ℝ) + ‖v‖) ∧ y ∈ U ∧
      ∀ y' ∈ U, ⟪bb, y' - y⟫_ℝ ≤ ε * ‖y' - y‖ := by
  set L : ℝ := (K : ℝ) + ‖v‖ with hL
  have hL0 : 0 ≤ L := by positivity
  set s : ℝ := 64 * (L + 1) ^ 2 / ρ ^ 2 with hs
  have hs0 : 0 < s := by positivity
  have hsρ : s * ρ ^ 2 = 64 * (L + 1) ^ 2 := by rw [hs]; field_simp
  set Φ : E n × E n → ℝ := fun q => J q.1 - ⟪v, q.1⟫_ℝ + ε * ‖q.2 - x‖ +
    s / 2 * ‖q.1 - q.2‖ ^ 2 + ‖q.1 - x‖ ^ 2 with hΦ
  set S : Set (E n × E n) := Metric.closedBall x ρ ×ˢ (U ∩ Metric.closedBall x ρ) with hS
  have hSc : IsCompact S :=
    (isCompact_closedBall x ρ).prod ((isCompact_closedBall x ρ).inter_left hUc)
  have hSne : S.Nonempty := ⟨(x, x), by simp [hS, hx, hρ.le]⟩
  have hΦl : LowerSemicontinuousOn Φ S := by
    apply LowerSemicontinuous.lowerSemicontinuousOn
    have h1 : LowerSemicontinuous (fun q : E n × E n => J q.1) := hJ.comp continuous_fst
    have h2 : Continuous (fun q : E n × E n => -⟪v, q.1⟫_ℝ + ε * ‖q.2 - x‖ +
        s / 2 * ‖q.1 - q.2‖ ^ 2 + ‖q.1 - x‖ ^ 2) := by fun_prop
    have h3 := h1.add h2.lowerSemicontinuous
    have heq : Φ = fun q : E n × E n => J q.1 + (-⟪v, q.1⟫_ℝ + ε * ‖q.2 - x‖ +
        s / 2 * ‖q.1 - q.2‖ ^ 2 + ‖q.1 - x‖ ^ 2) := by
      funext q; simp only [hΦ]; ring
    rw [heq]; exact h3
  obtain ⟨⟨z, y⟩, hzy, hmn⟩ := hΦl.exists_isMinOn hSne hSc
  have hz : ‖z - x‖ ≤ ρ := by
    have := hzy.1; rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hyU : y ∈ U := hzy.2.1
  have hy : ‖y - x‖ ≤ ρ := by
    have := hzy.2.2; rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hzt : z ∈ t := hball (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz)
  have hyt : y ∈ t := hball (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy)
  have hmin' : ∀ q ∈ S, Φ (z, y) ≤ Φ q := fun q hq => hmn hq
  set d := ‖z - y‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  -- comparison with `(x, x)`
  have hxx0 := hmin' (x, x) (by simp [hS, hx, hρ.le])
  have hxx : J z - ⟪v, z⟫_ℝ + ε * ‖y - x‖ + s / 2 * d ^ 2 + ‖z - x‖ ^ 2 ≤
      J x - ⟪v, x⟫_ℝ := by
    simp only [hΦ, sub_self, norm_zero] at hxx0
    norm_num at hxx0
    exact hxx0
  have hlipJ : J y - K * d ≤ J z := by
    have := hK.dist_le_mul z hzt y hyt
    rw [Real.dist_eq, dist_eq_norm] at this
    have := neg_abs_le (J z - J y)
    linarith
  have hvzy : ⟪v, z⟫_ℝ - ⟪v, y⟫_ℝ ≤ ‖v‖ * d := by
    rw [← inner_sub_right]; exact real_inner_le_norm _ _
  have hloc := hmin y hyU hy
  have hLd : L * d = (K : ℝ) * d + ‖v‖ * d := by rw [hL]; ring
  have hE1 : s / 2 * d ^ 2 + ‖z - x‖ ^ 2 ≤ L * d := by
    linarith only [hxx, hlipJ, hvzy, hloc, hLd]
  have hzz := sq_nonneg ‖z - x‖
  have hsd : s * d ≤ 2 * L := by
    rcases hd0.lt_or_eq with hpos | hzero
    · have h1 : (s / 2 * d) * d ≤ L * d := by linarith only [hE1, hzz]
      have h2 := le_of_mul_le_mul_right h1 hpos
      linarith only [h2]
    · rw [← hzero]; simp only [mul_zero]; linarith only [hL0]
  have hdρ : 32 * (L + 1) * d ≤ ρ ^ 2 := by
    have h1 : s * d * ρ ^ 2 ≤ 2 * L * ρ ^ 2 := mul_le_mul_of_nonneg_right hsd (sq_nonneg _)
    have h2 : s * d * ρ ^ 2 = 64 * (L + 1) ^ 2 * d := by rw [mul_right_comm, hsρ]
    have h3 : 2 * L * ρ ^ 2 ≤ 2 * (L + 1) * ρ ^ 2 := by nlinarith only [sq_nonneg ρ]
    have h4 : (2 * (L + 1)) * (32 * (L + 1) * d) ≤ (2 * (L + 1)) * ρ ^ 2 := by
      nlinarith only [h1, h2, h3]
    exact le_of_mul_le_mul_left h4 (by linarith only [hL0])
  have hzx2 : ‖z - x‖ ^ 2 ≤ ρ ^ 2 / 32 := by
    have h0 : L * d ≤ (L + 1) * d := by nlinarith only [hd0]
    have h1 : (L + 1) * d ≤ ρ ^ 2 / 32 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith only [hdρ]
    have h2 : s / 2 * d ^ 2 ≥ 0 := by positivity
    linarith only [hE1, h0, h1, h2]
  have hzx : ‖z - x‖ < ρ / 2 := by
    have hn := norm_nonneg (z - x)
    nlinarith only [hzx2, hn, hρ]
  have hdsmall : d ≤ ρ / 32 := by
    have h1 : d ≤ ρ ^ 2 / 32 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith only [hdρ, hd0, hL0]
    have h2 : ρ ^ 2 ≤ ρ := by nlinarith only [hρ, hρ1]
    linarith only [h1, h2]
  have hyx : ‖y - x‖ < ρ := by
    have := norm_sub_le_norm_sub_add_norm_sub y z x
    rw [norm_sub_rev y z] at this
    linarith
  -- the regular subgradient at `z`
  set a : E n := v - s • (z - y) - (2 : ℝ) • (z - x) with ha
  have hreg : IsRegularSubgrad (fun x => (J x : EReal)) z a := by
    apply regular_of_quad J z a (ρ / 2) (s / 2 + 1) (by linarith) (by positivity)
    intro z' hz'
    have hz'x : ‖z' - x‖ ≤ ρ := by
      have := norm_sub_le_norm_sub_add_norm_sub z' z x
      linarith
    have hcmp := hmin' (z', y) ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz'x, hzy.2⟩
    simp only [hΦ] at hcmp
    have e1 : z' - y = (z - y) + (z' - z) := by abel
    have e2 : z' - x = (z - x) + (z' - z) := by abel
    rw [e1, e2, norm_add_sq_real, norm_add_sq_real] at hcmp
    have e3 : ⟪a, z' - z⟫_ℝ = ⟪v, z'⟫_ℝ - ⟪v, z⟫_ℝ - s * ⟪z - y, z' - z⟫_ℝ -
        2 * ⟪z - x, z' - z⟫_ℝ := by
      rw [ha, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        inner_sub_right]
    rw [e3]
    nlinarith
  have hyx34 : ‖y - x‖ ≤ 3 * ρ / 4 := by
    have := norm_sub_le_norm_sub_add_norm_sub y z x
    rw [norm_sub_rev y z] at this
    linarith only [this, hzx, hdsmall, hρ]
  -- the approximate normal at `y`
  set bb : E n := s • (z - y) with hbb
  have hnormal : ∀ y' ∈ U, ⟪bb, y' - y⟫_ℝ ≤ ε * ‖y' - y‖ := by
    intro y' hy'
    set D := ‖y' - y‖ with hD
    rcases (norm_nonneg (y' - y)).lt_or_eq with hDpos | hDzero
    · have key : ∀ l, 0 < l → l ≤ min 1 (ρ / (4 * D)) →
          ⟪bb, y' - y⟫_ℝ ≤ ε * D + l * (s / 2 * D ^ 2) := by
        intro l hl hl0
        have hl1 : l ≤ 1 := hl0.trans (min_le_left _ _)
        have hl2 : l ≤ ρ / (4 * D) := hl0.trans (min_le_right _ _)
        have hlD : l * D ≤ ρ / 4 := by
          rw [le_div_iff₀ (by positivity)] at hl2; linarith
        set yl := y + l • (y' - y) with hyl
        have hylU : yl ∈ U := hU.add_smul_sub_mem hyU hy' ⟨hl.le, hl1⟩
        have hylx : ‖yl - x‖ ≤ ‖y - x‖ + l * D := by
          have : yl - x = (y - x) + l • (y' - y) := by rw [hyl]; abel
          rw [this]
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hl.le]
        have hylρ : ‖yl - x‖ ≤ ρ := by linarith only [hylx, hlD, hyx34]
        have hcmp := hmin' (z, yl) ⟨hzy.1, hylU,
          by rw [Metric.mem_closedBall, dist_eq_norm]; exact hylρ⟩
        simp only [hΦ] at hcmp
        have e1 : z - yl = (z - y) - l • (y' - y) := by rw [hyl]; abel
        rw [e1, norm_sub_sq_real (z - y) (l • (y' - y)), norm_smul, Real.norm_of_nonneg hl.le,
          real_inner_smul_right] at hcmp
        have hbbi : ⟪bb, y' - y⟫_ℝ = s * ⟪z - y, y' - y⟫_ℝ := by
          rw [hbb, real_inner_smul_left]
        rw [hbbi]
        have hε' := mul_le_mul_of_nonneg_left hylx hε.le
        have : l * (s * ⟪z - y, y' - y⟫_ℝ) ≤ l * (ε * D + l * (s / 2 * D ^ 2)) := by
          nlinarith
        exact le_of_mul_le_mul_left this hl
      exact le_of_small _ _ _ _ (lt_min one_pos (by positivity)) (by positivity) key
    · have : y' = y := by
        have := hDzero.symm; rw [norm_eq_zero, sub_eq_zero] at this; exact this
      subst this
      simp only [sub_self, inner_zero_right]
      exact mul_nonneg hε.le (norm_nonneg _)
  refine ⟨z, y, a, bb, by linarith, hyx, hreg, ?_, ?_, hyU, hnormal⟩
  · rw [ha, hbb]; abel
  · rw [hbb, norm_smul, Real.norm_of_nonneg hs0.le]
    linarith

/-- Sum rule for `J + ι_U` (J locally Lipschitz, U closed convex): a Fréchet-type subgradient
`v` of `J` relative to `U` at `x` splits as `a + b` with `a ∈ ∂J(x)` (limiting) and
`b ∈ N_U(x)`. -/
theorem sum_rule {n : ℕ} (J : E n → ℝ) (hJ : LowerSemicontinuous J) (U : Set (E n))
    (hU : Convex ℝ U) (hUc : IsClosed U) (x : E n) (hx : x ∈ U)
    (hLip : ∃ K : NNReal, ∃ t ∈ 𝓝 x, LipschitzOnWith K J t) (v : E n)
    (hv : ∀ ε > 0, ∀ᶠ z in 𝓝 x, z ∈ U → J x ≤ J z - ⟪v, z - x⟫_ℝ + ε * ‖z - x‖) :
    ∃ a ∈ LimitingSubdiff (fun z => (J z : EReal)) x, ∃ b ∈ normalCone U x, v = a + b := by
  obtain ⟨K, t, ht, hK⟩ := hLip
  obtain ⟨r0, hr0, hr0t⟩ := Metric.mem_nhds_iff.1 ht
  set r1 := min (r0 / 2) 1 with hr1def
  have hr1 : 0 < r1 := lt_min (by linarith) one_pos
  have hball1 : Metric.closedBall x r1 ⊆ t := by
    intro z hz
    apply hr0t
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have := min_le_left (r0 / 2) 1
    linarith
  have hρ : ∀ j : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r1 ∧ ρ ≤ 1 / ((j : ℝ) + 1) ∧
      ∀ y ∈ U, ‖y - x‖ ≤ ρ → J x - ⟪v, x⟫_ℝ ≤ J y - ⟪v, y⟫_ℝ + 1 / ((j : ℝ) + 1) * ‖y - x‖ := by
    intro j
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hv (1 / ((j : ℝ) + 1)) (by positivity))
    refine ⟨min (δ / 2) (min r1 (1 / ((j : ℝ) + 1))), lt_min (by linarith) (lt_min hr1 (by positivity)),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _),
      fun y hy hyx => ?_⟩
    have hd : dist y x < δ := by
      rw [dist_eq_norm]
      have := min_le_left (δ / 2) (min r1 (1 / ((j : ℝ) + 1)))
      linarith
    have h := hδ' hd hy
    rw [inner_sub_right] at h
    linarith
  choose ρ hρpos hρr1 hρj hρmin using hρ
  have hst : ∀ j : ℕ, ∃ z y a bb : E n, ‖z - x‖ < ρ j ∧ ‖y - x‖ < ρ j ∧
      IsRegularSubgrad (fun x => (J x : EReal)) z a ∧
      v = a + bb + (2 : ℝ) • (z - x) ∧ ‖bb‖ ≤ 2 * ((K : ℝ) + ‖v‖) ∧ y ∈ U ∧
      ∀ y' ∈ U, ⟪bb, y' - y⟫_ℝ ≤ 1 / ((j : ℝ) + 1) * ‖y' - y‖ := fun j =>
    step J hJ U hU hUc x hx v K t hK (ρ j) (1 / ((j : ℝ) + 1)) (hρpos j)
      ((hρr1 j).trans (min_le_right _ _)) (by positivity)
      ((Metric.closedBall_subset_closedBall (hρr1 j)).trans hball1) (hρmin j)
  choose z y a bb hz hy hreg hsum hbb hyU hnorm using hst
  obtain ⟨b, -, φ, hφ, hbφ⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_closedBall (x := (0 : E n)) (r := 2 * ((K : ℝ) + ‖v‖)))
    (fun j => mem_closedBall_zero_iff.2 (hbb j))
  have hε0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hzx : Tendsto z atTop (𝓝 x) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun j => (hz j).le.trans (hρj j)) hε0)
  have hyx : Tendsto y atTop (𝓝 x) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun j => (hy j).le.trans (hρj j)) hε0)
  have hφt := hφ.tendsto_atTop
  have hJz : Tendsto (fun j => J (z j)) atTop (𝓝 (J x)) := by
    have hxt : x ∈ t := hball1 (Metric.mem_closedBall_self hr1.le)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun j => (K : ℝ) * ‖z j - x‖) atTop (𝓝 ((K : ℝ) * ‖x - x‖)) :=
      ((hzx.sub_const x).norm).const_mul (K : ℝ)
    rw [sub_self, norm_zero, mul_zero] at hlim
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim
    have hzt : z j ∈ t := hball1 (by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact (hz j).le.trans (hρr1 j))
    have := hK.dist_le_mul (z j) hzt x hxt
    rwa [dist_eq_norm, dist_eq_norm] at this
  refine ⟨v - b, ⟨EReal.coe_ne_top _, z ∘ φ, a ∘ φ, hzx.comp hφt, ?_, ?_, fun j => hreg (φ j)⟩,
    b, ⟨hx, fun ζ hζ => ?_⟩, by abel⟩
  · exact (continuous_coe_real_ereal.tendsto _).comp (hJz.comp hφt)
  · have ha : ∀ j, a j = v - bb j - (2 : ℝ) • (z j - x) := fun j => by
      rw [hsum j]; abel
    have h := (tendsto_const_nhds (x := v)).sub hbφ |>.sub
      (((hzx.comp hφt).sub_const x).const_smul (2 : ℝ))
    simp only [sub_self, smul_zero, sub_zero] at h
    refine h.congr (fun j => ?_)
    simp only [Function.comp_apply, ha]
  · have hlim : Tendsto (fun j => ⟪bb (φ j), ζ - y (φ j)⟫_ℝ -
        1 / ((φ j : ℝ) + 1) * ‖ζ - y (φ j)‖) atTop (𝓝 (⟪b, ζ - x⟫_ℝ - 0 * ‖ζ - x‖)) := by
      have h1 : Tendsto (fun j => ζ - y (φ j)) atTop (𝓝 (ζ - x)) :=
        tendsto_const_nhds.sub (hyx.comp hφt)
      exact (hbφ.inner h1).sub ((hε0.comp hφt).mul h1.norm)
    simp only [zero_mul, sub_zero] at hlim
    refine le_of_tendsto' hlim (fun j => ?_)
    have := hnorm (φ j) ζ hζ
    linarith

/-! ### Smooth estimates (several follow the accepted platform proofs of Lemmas 4.2/4.3) -/

theorem scalar_upper (g dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (dg t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, dg t - dg 0 ≤ L * t) :
    g 1 - g 0 ≤ dg 0 + L / 2 := by
  let f := fun t => g t - dg 0 * t - L / 2 * t ^ 2
  have hf (t : ℝ) : HasDerivAt f (dg t - dg 0 - L * t) t := by
    convert! ((hd t).sub ((hasDerivAt_id t).const_mul (dg 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1
    dsimp [f]
    ring
  have ha : AntitoneOn f (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hf t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf t).deriv]
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      linarith only [hb t ht']
  have h := ha (by simp : (0 : ℝ) ∈ Set.Icc 0 1) (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  dsimp [f] at h
  norm_num at h
  linarith

theorem gradient_upper {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → ℝ) (L : ℝ) (hf : Differentiable ℝ f)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : X) :
    f y - f x - ⟪gradient f x, y - x⟫_ℝ ≤ L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let g := fun t : ℝ => f (x + t • d)
  let dg := fun t : ℝ => ⟪gradient f (x + t • d), d⟫_ℝ
  have hd (t : ℝ) : HasDerivAt g (dg t) t := by
    have hh := (hf _).hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const d).const_add x)
    convert! hh using 1
    simp only [dg, inner_gradient_left, id_eq, one_smul]
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : dg t - dg 0 ≤ (L * ‖d‖ ^ 2) * t := by
    dsimp [dg]
    simp only [zero_smul, add_zero, ← inner_sub_left]
    calc
      _ ≤ ‖gradient f (x + t • d) - gradient f x‖ * ‖d‖ := real_inner_le_norm _ _
      _ ≤ (L * ‖(x + t • d) - x‖) * ‖d‖ := mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)
      _ = _ := by rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]; ring
  have hh := scalar_upper g dg (L * ‖d‖ ^ 2) hd hb
  dsimp [g, dg, d] at hh
  simp only [zero_smul, one_smul, add_zero, add_sub_cancel] at hh
  linarith

theorem euclidean_norm_le_sum {m : ℕ} (x : E m) : ‖x‖ ≤ ∑ j, ‖x j‖ := by
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun j : Fin m => ‖x j‖) (fun _ _ => norm_nonneg _)
  have hn := EuclideanSpace.norm_sq_eq x
  have hp : 0 ≤ ∑ j : Fin m, ‖x j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith

theorem coordinate_fderiv {n m : ℕ} (f : E n → E m) (hf : Differentiable ℝ f)
    (a z : E n) (j : Fin m) :
    fderiv ℝ (fun x => f x j) a z = (fderiv ℝ f a z) j := by
  have hh := ((PiLp.proj 2 (fun _ : Fin m => ℝ) j).hasFDerivAt.comp a (hf a).hasFDerivAt).fderiv
  exact congrArg (fun F : E n →L[ℝ] ℝ => F z) hh

theorem Om_fderiv_lipschitz {n d m : ℕ} (P : Problem n d m) (L : Fin m → ℝ)
    (hOm : Differentiable ℝ P.Om)
    (hL : ∀ j, 0 ≤ L j ∧ ∀ a b,
      ‖gradient (fun x => P.Om x j) a - gradient (fun x => P.Om x j) b‖ ≤ L j * ‖a - b‖)
    (a b : E n) : ‖fderiv ℝ P.Om a - fderiv ℝ P.Om b‖ ≤ LOm L * ‖a - b‖ := by
  have hn : 0 ≤ LOm L := Finset.sum_nonneg (fun j _ => (hL j).1)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hn (norm_nonneg _))
  intro z
  have hi (j : Fin m) :
      ‖((fderiv ℝ P.Om a - fderiv ℝ P.Om b) z) j‖ ≤ L j * ‖a - b‖ * ‖z‖ := by
    have he : ((fderiv ℝ P.Om a - fderiv ℝ P.Om b) z) j =
        ⟪gradient (fun x => P.Om x j) a - gradient (fun x => P.Om x j) b, z⟫_ℝ := by
      rw [inner_sub_left, inner_gradient_left, inner_gradient_left,
        coordinate_fderiv P.Om hOm, coordinate_fderiv P.Om hOm]
      rfl
    rw [he]
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right ((hL j).2 a b) (norm_nonneg z))
  calc
    _ ≤ ∑ j, ‖((fderiv ℝ P.Om a - fderiv ℝ P.Om b) z) j‖ := euclidean_norm_le_sum _
    _ ≤ ∑ j, L j * ‖a - b‖ * ‖z‖ := Finset.sum_le_sum (fun j _ => hi j)
    _ = LOm L * ‖a - b‖ * ‖z‖ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

theorem quadratic_minimum {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (B : X →L[ℝ] Y) (g : X) (q : Y) (γ : ℝ) (v y : X)
    (hmin : ∀ z, ⟪g, y⟫_ℝ + ⟪q, B y⟫_ℝ + γ / 2 * ‖B (y - v)‖ ^ 2 ≤
      ⟪g, z⟫_ℝ + ⟪q, B z⟫_ℝ + γ / 2 * ‖B (z - v)‖ ^ 2) :
    g + ContinuousLinearMap.adjoint B q + γ • ContinuousLinearMap.adjoint B (B (y - v)) = 0 := by
  let z := g + ContinuousLinearMap.adjoint B q + γ • ContinuousLinearMap.adjoint B (B (y - v))
  have hd := (((innerSL ℝ g).hasFDerivAt).add
    (((innerSL ℝ q).comp B).hasFDerivAt)).add
    (((B.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const v)).norm_sq).const_mul (γ / 2))
  have hm : IsLocalMin (fun z => ⟪g, z⟫_ℝ + ⟪q, B z⟫_ℝ + γ / 2 * ‖B (z - v)‖ ^ 2) y :=
    Filter.Eventually.of_forall hmin
  have hh := congrArg (fun f : X →L[ℝ] ℝ => f z) (hd.fderiv.symm.trans hm.fderiv_eq_zero)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change ⟪z, z⟫_ℝ = 0
  calc
    _ = ⟪g, z⟫_ℝ + ⟪q, B z⟫_ℝ + γ * ⟪B (y - v), B z⟫_ℝ := by
      simp only [z, inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
    _ = 0 := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.zero_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
        id_eq] at hh
      nlinarith only [hh]

theorem grad_bounds {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) (v v' : E d) :
    ‖gradU P u v - gradU P u' v'‖ ≤ LG * (‖u - u'‖ + ‖v - v'‖) ∧
      ‖gradV P u v - gradV P u' v'‖ ≤ LG * (‖u - u'‖ + ‖v - v'‖) := by
  have h := hA1.1.2.2 u v u' v'
  have hnn := mul_nonneg (sq_nonneg LG) (mul_nonneg (norm_nonneg (u - u')) (norm_nonneg (v - v')))
  have hLG := hA1.1.2.1
  have hp : 0 ≤ LG * (‖u - u'‖ + ‖v - v'‖) :=
    mul_nonneg hLG (add_nonneg (norm_nonneg _) (norm_nonneg _))
  constructor
  · nlinarith only [h, hnn, hp, norm_nonneg (gradU P u v - gradU P u' v'),
      sq_nonneg ‖gradV P u v - gradV P u' v'‖]
  · nlinarith only [h, hnn, hp, norm_nonneg (gradV P u v - gradV P u' v'),
      sq_nonneg ‖gradU P u v - gradU P u' v'‖]

theorem adjoint_apply_norm_le {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (y : Y) : ‖ContinuousLinearMap.adjoint A y‖ ≤ ‖A‖ * ‖y‖ := by
  calc _ ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖A‖ * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]

end NAPPALP31

open NAPPALP31 in
set_option maxHeartbeats 4000000 in
theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : NAPPAL.KL.E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) (k : ℕ) :
    NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u (k + 1), v (k + 1), p (k + 1))) ≤
      ENNReal.ofReal (Real.sqrt 3 * NAPPAL.Rate.hfun P LG LH L0 (NAPPAL.KL.LOm LOmj) LK γ σ (NAPPAL.Rate.qseq P γ u v p k) (δ k) *
        NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))) := by
  have hA1 := hrun.1
  have hN := hrun.2.2.1
  obtain ⟨hK, hβ, -, hLK, hKlip, -⟩ := hrun.2.1
  obtain ⟨hγ, hσ, -, hNk⟩ := hN
  obtain ⟨⟨hδ, hσδ, -⟩, ⟨hxU, hopt5⟩, hopt6, hp⟩ := hNk k
  have hJlsc := hA1.2.2.1.1
  have hJlip := hA1.2.2.1.2.1
  have hUconv := hA1.2.2.1.2.2.1
  have hUcl := hA1.2.2.1.2.2.2
  have hOm := hA1.2.2.2.1.1
  have hPhi := hA1.2.2.2.1.2.1
  have hL0 := hA1.2.2.2.1.2.2.1
  have hTh := hA1.2.2.2.1.2.2.2
  have hOmj := hA1.2.2.2.2.1
  have hLG := hA1.1.2.1
  have hLH := hA1.2.1.2.1
  have hLOm : 0 ≤ LOm LOmj := Finset.sum_nonneg (fun j _ => (hOmj j).1)
  set x := u (k + 1) with hx
  set uk := u k with huk
  set vk := v k with hvk
  set vx := v (k + 1) with hvx
  set px := p (k + 1) with hpx
  set pk := p k with hpk
  set q := qseq P γ u v p k with hq
  set εk := ε k with hεkdef
  have hεk : 0 < εk := lt_of_lt_of_le (mul_pos hσ hδ) hσδ
  set gU := gradU P uk vk with hgU
  set gs : E n := gU + ContinuousLinearMap.adjoint (fderiv ℝ P.Om uk) q +
    ContinuousLinearMap.adjoint (fderiv ℝ P.Phi x) q + εk⁻¹ • (gradient K x - gradient K uk) with hgs
  have hexp : ∀ z, obj5 P K uk vk q εk z - obj5 P K uk vk q εk x - (P.J z - P.J x) -
      ⟪gs, z - x⟫_ℝ = ⟪q, P.Phi z - P.Phi x - fderiv ℝ P.Phi x (z - x)⟫_ℝ +
        (K z - K x - ⟪gradient K x, z - x⟫_ℝ) / εk := by
    intro z
    simp only [obj5, bregman, hgs, inner_add_left, real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left, inner_add_right, inner_sub_right, map_sub,
      inner_sub_left]
    field_simp
    ring
  -- Fréchet optimality of the `u`-subproblem
  have hv : ∀ ε' > 0, ∀ᶠ z in 𝓝 x, z ∈ P.U →
      P.J x ≤ P.J z - ⟪-gs, z - x⟫_ℝ + ε' * ‖z - x‖ := by
    intro ε' hε'
    have hc : 0 < ε' / (2 * (‖q‖ + 1)) := by positivity
    have hPhiO := ((hPhi x).hasFDerivAt.isLittleO).def hc
    have hr : 0 < ε' / (LK / εk + 1) := by positivity
    have hball : ∀ᶠ z in 𝓝 x, ‖z - x‖ < ε' / (LK / εk + 1) := by
      filter_upwards [Metric.ball_mem_nhds x hr] with z hz
      rwa [Metric.mem_ball, dist_eq_norm] at hz
    filter_upwards [hPhiO, hball] with z h1 h2 hzU
    have hopt := hopt5 z hzU
    have he := hexp z
    have hq1 : ⟪q, P.Phi z - P.Phi x - fderiv ℝ P.Phi x (z - x)⟫_ℝ ≤
        ‖q‖ * (ε' / (2 * (‖q‖ + 1)) * ‖z - x‖) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    have hq2 : ‖q‖ * (ε' / (2 * (‖q‖ + 1)) * ‖z - x‖) ≤ ε' / 2 * ‖z - x‖ := by
      have h3 : ‖q‖ * (ε' / (2 * (‖q‖ + 1))) ≤ ε' / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [norm_nonneg q]
      calc _ = (‖q‖ * (ε' / (2 * (‖q‖ + 1)))) * ‖z - x‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    have hK2 := gradient_upper K LK hK hKlip x z
    have hK3 : (K z - K x - ⟪gradient K x, z - x⟫_ℝ) / εk ≤ ε' / 2 * ‖z - x‖ := by
      rw [div_le_iff₀ hεk]
      have hn := norm_nonneg (z - x)
      have h4 : (LK / εk + 1) * ‖z - x‖ ≤ ε' := by
        rw [lt_div_iff₀ (by positivity)] at h2; linarith
      have h5 : LK * ‖z - x‖ ≤ ε' * εk := by
        have : LK / εk * ‖z - x‖ ≤ ε' := by nlinarith
        rw [div_mul_eq_mul_div, div_le_iff₀ hεk] at this
        linarith
      nlinarith
    rw [inner_neg_left]
    have hobj : obj5 P K uk vk q εk x ≤ obj5 P K uk vk q εk z := hopt
    linarith
  obtain ⟨a, ha, b, hb, hab⟩ := sum_rule P.J hJlsc P.U hUconv hUcl x hxU (hJlip x hxU) (-gs) hv
  -- the residual vector
  set yp := px + γ • (Theta P x + P.B vx) with hyp
  set ξ : W n d m := (gradU P x vx + a + b + ContinuousLinearMap.adjoint (jac P x) yp,
    gradV P x vx + gradient P.H vx + ContinuousLinearMap.adjoint P.B yp,
    Theta P x + P.B vx) with hξdef
  have hξ : ξ ∈ dAugLag P γ (x, vx, px) := ⟨a, ha, b, hb, rfl, rfl, rfl⟩
  have hdist : distZero (dAugLag P γ (x, vx, px)) ≤ ENNReal.ofReal (tnorm ξ) := iInf₂_le ξ hξ
  refine hdist.trans (ENNReal.ofReal_le_ofReal ?_)
  set Du := ‖uk - x‖ with hDu
  set Dv := ‖vk - vx‖ with hDv
  set Dp := ‖pk - px‖ with hDp
  have hDu0 : 0 ≤ Du := norm_nonneg _
  have hDv0 : 0 ≤ Dv := norm_nonneg _
  have hDp0 : 0 ≤ Dp := norm_nonneg _
  -- Jacobian facts
  have hjac : jac P x = fderiv ℝ P.Om x + fderiv ℝ P.Phi x := by
    show fderiv ℝ (fun u => P.Om u + P.Phi u) x = _
    exact fderiv_add (hOm x) (hPhi x)
  have hjacn : ‖jac P x‖ ≤ L0 := by
    have hlip : LipschitzWith ⟨L0, hL0⟩ (Theta P) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [dist_eq_norm, dist_eq_norm]; exact hTh a b
    exact norm_fderiv_le_of_lipschitz ℝ hlip
  -- `yp - q`
  have hyq : yp - q = (px - pk) + γ • ((Theta P x - Theta P uk) + P.B (vx - vk)) := by
    rw [hyp, hq, qseq, map_sub]; module
  have hyqn : ‖yp - q‖ ≤ Dp + γ * (L0 * Du + ‖P.B‖ * Dv) := by
    rw [hyq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hγ.le, norm_sub_rev px pk]
    have h1 : ‖Theta P x - Theta P uk‖ ≤ L0 * Du := by rw [hDu, norm_sub_rev]; exact hTh _ _
    have h2 : ‖P.B (vx - vk)‖ ≤ ‖P.B‖ * Dv := by
      rw [hDv, norm_sub_rev]; exact P.B.le_opNorm _
    have h3 := norm_add_le (Theta P x - Theta P uk) (P.B (vx - vk))
    have h4 : γ * ‖Theta P x - Theta P uk + P.B (vx - vk)‖ ≤ γ * (L0 * Du + ‖P.B‖ * Dv) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ.le
    linarith
  -- first block
  have hid1 : ξ.1 = (gradU P x vx - gU) +
      ContinuousLinearMap.adjoint (fderiv ℝ P.Om x - fderiv ℝ P.Om uk) q +
      ContinuousLinearMap.adjoint (jac P x) (yp - q) - εk⁻¹ • (gradient K x - gradient K uk) := by
    have hab' : a + b = -gs := hab.symm
    show gradU P x vx + a + b + ContinuousLinearMap.adjoint (jac P x) yp = _
    rw [add_assoc (gradU P x vx) a b, hab', hgs, hjac]
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    abel
  have hT1 : ‖gradU P x vx - gU‖ ≤ LG * (Du + Dv) := by
    have := (grad_bounds P LG LH L0 LOmj hA1 x uk vx vk).1
    rwa [norm_sub_rev x uk, norm_sub_rev vx vk] at this
  have hT2 : ‖ContinuousLinearMap.adjoint (fderiv ℝ P.Om x - fderiv ℝ P.Om uk) q‖ ≤
      LOm LOmj * Du * ‖q‖ := by
    refine (adjoint_apply_norm_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have := Om_fderiv_lipschitz P LOmj hOm hOmj x uk
    rwa [norm_sub_rev x uk] at this
  have hT3 : ‖ContinuousLinearMap.adjoint (jac P x) (yp - q)‖ ≤
      L0 * (Dp + γ * (L0 * Du + ‖P.B‖ * Dv)) :=
    (adjoint_apply_norm_le _ _).trans (mul_le_mul hjacn hyqn (norm_nonneg _) hL0)
  have hT4 : ‖εk⁻¹ • (gradient K x - gradient K uk)‖ ≤ LK / (σ * δ k) * Du := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hεk.le)]
    have h1 : ‖gradient K x - gradient K uk‖ ≤ LK * Du := by
      rw [hDu, norm_sub_rev uk x]; exact hKlip x uk
    have h2 : εk⁻¹ ≤ (σ * δ k)⁻¹ := inv_anti₀ (mul_pos hσ hδ) hσδ
    calc εk⁻¹ * ‖gradient K x - gradient K uk‖ ≤ (σ * δ k)⁻¹ * (LK * Du) :=
          mul_le_mul h2 h1 (norm_nonneg _) (inv_nonneg.2 (mul_pos hσ hδ).le)
      _ = LK / (σ * δ k) * Du := by rw [div_eq_mul_inv]; ring
  have hξ1 : ‖ξ.1‖ ≤ (LG + ‖q‖ * LOm LOmj + γ * L0 ^ 2 + LK / (σ * δ k)) * Du +
      (LG + γ * ‖P.B‖ * L0) * Dv + L0 * Dp := by
    rw [hid1]
    have := norm_sub_le (gradU P x vx - gU +
      ContinuousLinearMap.adjoint (fderiv ℝ P.Om x - fderiv ℝ P.Om uk) q +
      ContinuousLinearMap.adjoint (jac P x) (yp - q)) (εk⁻¹ • (gradient K x - gradient K uk))
    have h2 := norm_add_le (gradU P x vx - gU +
      ContinuousLinearMap.adjoint (fderiv ℝ P.Om x - fderiv ℝ P.Om uk) q)
      (ContinuousLinearMap.adjoint (jac P x) (yp - q))
    have h3 := norm_add_le (gradU P x vx - gU)
      (ContinuousLinearMap.adjoint (fderiv ℝ P.Om x - fderiv ℝ P.Om uk) q)
    nlinarith only [this, h2, h3, hT1, hT2, hT3, hT4]
  -- second block
  have hq0 := quadratic_minimum P.B (gradV P uk vk + gradient P.H vk) q γ vk vx hopt6
  have hid2 : ξ.2.1 = (gradV P x vx - gradV P uk vk) + (gradient P.H vx - gradient P.H vk) +
      ContinuousLinearMap.adjoint P.B (px - pk) +
      γ • ContinuousLinearMap.adjoint P.B (Theta P x - Theta P uk) := by
    show gradV P x vx + gradient P.H vx + ContinuousLinearMap.adjoint P.B yp = _
    have h0 : gradV P x vx + gradient P.H vx + ContinuousLinearMap.adjoint P.B yp =
        gradV P x vx + gradient P.H vx + ContinuousLinearMap.adjoint P.B yp -
          (gradV P uk vk + gradient P.H vk + ContinuousLinearMap.adjoint P.B q +
            γ • ContinuousLinearMap.adjoint P.B (P.B (vx - vk))) := by
      rw [hq0, sub_zero]
    rw [h0, hyp, hq, qseq]
    simp only [map_add, map_sub, map_smul]
    module
  have hS1 : ‖gradV P x vx - gradV P uk vk‖ ≤ LG * (Du + Dv) := by
    have := (grad_bounds P LG LH L0 LOmj hA1 x uk vx vk).2
    rwa [norm_sub_rev x uk, norm_sub_rev vx vk] at this
  have hS2 : ‖gradient P.H vx - gradient P.H vk‖ ≤ LH * Dv := by
    rw [hDv, norm_sub_rev vk vx]; exact hA1.2.1.2.2 vx vk
  have hS3 : ‖ContinuousLinearMap.adjoint P.B (px - pk)‖ ≤ ‖P.B‖ * Dp := by
    refine (adjoint_apply_norm_le _ _).trans ?_
    rw [hDp, norm_sub_rev pk px]
  have hS4 : ‖γ • ContinuousLinearMap.adjoint P.B (Theta P x - Theta P uk)‖ ≤
      γ * (‖P.B‖ * (L0 * Du)) := by
    rw [norm_smul, Real.norm_of_nonneg hγ.le]
    refine mul_le_mul_of_nonneg_left ((adjoint_apply_norm_le _ _).trans ?_) hγ.le
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [hDu, norm_sub_rev uk x]; exact hTh _ _
  have hξ2 : ‖ξ.2.1‖ ≤ (LG + γ * ‖P.B‖ * L0) * Du + (LG + LH) * Dv + ‖P.B‖ * Dp := by
    rw [hid2]
    have h1 := norm_add_le (gradV P x vx - gradV P uk vk + (gradient P.H vx - gradient P.H vk) +
      ContinuousLinearMap.adjoint P.B (px - pk))
      (γ • ContinuousLinearMap.adjoint P.B (Theta P x - Theta P uk))
    have h2 := norm_add_le (gradV P x vx - gradV P uk vk + (gradient P.H vx - gradient P.H vk))
      (ContinuousLinearMap.adjoint P.B (px - pk))
    have h3 := norm_add_le (gradV P x vx - gradV P uk vk) (gradient P.H vx - gradient P.H vk)
    nlinarith only [h1, h2, h3, hS1, hS2, hS3, hS4]
  -- third block
  have hξ3 : ‖ξ.2.2‖ ≤ 1 / γ * Dp := by
    show ‖Theta P x + P.B vx‖ ≤ _
    have h : Theta P x + P.B vx = γ⁻¹ • (px - pk) := by
      rw [hp, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
    rw [h, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hγ.le), hDp, norm_sub_rev pk px]
    rw [one_div]
  -- assemble
  set H := NAPPAL.Rate.hfun P LG LH L0 (LOm LOmj) LK γ σ q (δ k) with hH
  have hH1 : 2 * LG + ‖q‖ * LOm LOmj + γ * ‖P.B‖ * L0 + γ * L0 ^ 2 + LK / (σ * δ k) ≤ H :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hH2 : 2 * LG + LH + γ * ‖P.B‖ * L0 ≤ H := (le_max_right _ _).trans (le_max_left _ _)
  have hH3 : L0 + ‖P.B‖ + 1 / γ ≤ H := le_max_right _ _
  have hH0 : 0 ≤ H := le_trans (by positivity) hH3
  have hsum : ‖ξ.1‖ + ‖ξ.2.1‖ + ‖ξ.2.2‖ ≤ H * (Du + Dv + Dp) := by
    have e1 := mul_le_mul_of_nonneg_right hH1 hDu0
    have e2 := mul_le_mul_of_nonneg_right hH2 hDv0
    have e3 := mul_le_mul_of_nonneg_right hH3 hDp0
    nlinarith only [hξ1, hξ2, hξ3, e1, e2, e3]
  have htn : tnorm ξ ≤ ‖ξ.1‖ + ‖ξ.2.1‖ + ‖ξ.2.2‖ := by
    unfold tnorm
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ‖ξ.1‖ + ‖ξ.2.1‖ + ‖ξ.2.2‖)]
    apply Real.sqrt_le_sqrt
    nlinarith [norm_nonneg ξ.1, norm_nonneg ξ.2.1, norm_nonneg ξ.2.2]
  have hw : Du + Dv + Dp ≤ Real.sqrt 3 * wdist (uk, vk, pk) (x, vx, px) := by
    unfold wdist tnorm
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Du + Dv + Dp)]
    apply Real.sqrt_le_sqrt
    rw [← hDu, ← hDv, ← hDp]
    nlinarith only [sq_nonneg (Du - Dv), sq_nonneg (Du - Dp), sq_nonneg (Dv - Dp)]
  calc tnorm ξ ≤ H * (Du + Dv + Dp) := htn.trans hsum
    _ ≤ H * (Real.sqrt 3 * wdist (uk, vk, pk) (x, vx, px)) := mul_le_mul_of_nonneg_left hw hH0
    _ = _ := by ring
