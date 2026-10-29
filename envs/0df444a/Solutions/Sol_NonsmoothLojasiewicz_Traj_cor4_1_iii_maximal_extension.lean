-- Prove2me | solution 1 for NonsmoothLojasiewicz.Traj.cor4_1_iii_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T23:03:16.61108+00:00
-- url     : https://prove2.me/submissions/beaadb10-9401-4171-a1a4-eb7cedd0d1ba

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace

namespace TrajLib

open NonconvexSplitting.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `ρ`-semiconvexity of `f` along segments of length `≤ δ` starting in `K` (real-bound form). -/
def SemiconvOn (f : E → EReal) (K : Set E) (ρ δ : ℝ) : Prop :=
  ∀ u ∈ K, ∀ y : E, ‖y - u‖ ≤ δ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ a b : ℝ, f u ≤ a → f y ≤ b →
    f (u + θ • (y - u)) ≤ (((1 - θ) * a + θ * b + ρ * θ * (1 - θ) * ‖y - u‖ ^ 2 : ℝ) : EReal)

/-- `u` minimizes `h f + ½‖· - x‖²` (stated with real bounds). -/
def IsProxPt (f : E → EReal) (h : ℝ) (x u : E) : Prop :=
  f u ≠ ⊤ ∧ f u ≠ ⊥ ∧ ∀ v : E, ∀ b : ℝ, f v ≤ b →
    h * (f u).toReal + ‖u - x‖ ^ 2 / 2 ≤ h * b + ‖v - x‖ ^ 2 / 2

lemma norm_sq_comb (p q : E) (θ : ℝ) :
    ‖(1 - θ) • p + θ • q‖ ^ 2 =
      (1 - θ) * ‖p‖ ^ 2 + θ * ‖q‖ ^ 2 - θ * (1 - θ) * ‖p - q‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm p q]
  ring

lemma le_of_forall_theta {c e d : ℝ}
    (H : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → c + (1 - θ) * e ≤ d) : c + e ≤ d := by
  by_contra hlt
  push Not at hlt
  have h1 := H 1 one_pos le_rfl
  have he : 0 < e := by nlinarith
  set θ := min 1 ((c + e - d) / (2 * e)) with hθdef
  have hθpos : 0 < θ := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hθle : θ ≤ 1 := min_le_left _ _
  have hθ2 : θ ≤ (c + e - d) / (2 * e) := min_le_right _ _
  have h3 := H θ hθpos hθle
  have h4 : θ * e ≤ (c + e - d) / 2 := by
    calc θ * e ≤ (c + e - d) / (2 * e) * e := mul_le_mul_of_nonneg_right hθ2 he.le
      _ = (c + e - d) / 2 := by field_simp
  nlinarith

/-- Three-point inequality for a proximal point of a locally semiconvex function. -/
theorem three_point {f : E → EReal} {K : Set E} {ρ δ h : ℝ} {x u y : E} {b : ℝ}
    (hS : SemiconvOn f K ρ δ) (hu : IsProxPt f h x u) (huK : u ∈ K) (hyu : ‖y - u‖ ≤ δ)
    (hb : f y ≤ b) :
    h * (f u).toReal + ‖u - x‖ ^ 2 / 2 + (1 / 2 - h * ρ) * ‖y - u‖ ^ 2
      ≤ h * b + ‖y - x‖ ^ 2 / 2 := by
  obtain ⟨hut, hub, hmin⟩ := hu
  set a := (f u).toReal with hadef
  have ha : f u ≤ (a : EReal) := by rw [hadef, EReal.coe_toReal hut hub]
  have key : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (h * a + ‖u - x‖ ^ 2 / 2) + (1 - θ) * ((1 / 2 - h * ρ) * ‖y - u‖ ^ 2)
        ≤ h * b + ‖y - x‖ ^ 2 / 2 := by
    intro θ hθ hθ1
    have h1 := hS u huK y hyu θ hθ.le hθ1 a b ha hb
    have h2 := hmin _ _ h1
    have hid : u + θ • (y - u) - x = (1 - θ) • (u - x) + θ • (y - x) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [hid, norm_sq_comb] at h2
    have hpq : (u - x) - (y - x) = -(y - u) := by abel
    rw [hpq, norm_neg] at h2
    have h3 : θ * ((h * a + ‖u - x‖ ^ 2 / 2) + (1 - θ) * ((1 / 2 - h * ρ) * ‖y - u‖ ^ 2))
        ≤ θ * (h * b + ‖y - x‖ ^ 2 / 2) := by
      linear_combination h2
    exact le_of_mul_le_mul_left h3 hθ
  have := le_of_forall_theta key
  linarith

lemma norm_sq_four (u u' x x' : E) :
    ‖u - x‖ ^ 2 + ‖u' - x'‖ ^ 2 - ‖u' - x‖ ^ 2 - ‖u - x'‖ ^ 2 = -2 * ⟪u - u', x - x'⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm x u, real_inner_comm x' u,
    real_inner_comm x u', real_inner_comm x' u']
  ring

/-- Monotonicity-type inequality between two proximal points. -/
theorem prox_inner_le {f : E → EReal} {K : Set E} {ρ δ h : ℝ} {x x' u u' : E}
    (hS : SemiconvOn f K ρ δ) (hu : IsProxPt f h x u) (hu' : IsProxPt f h x' u')
    (huK : u ∈ K) (hu'K : u' ∈ K) (hd : ‖u - u'‖ ≤ δ) :
    (1 - 2 * h * ρ) * ‖u - u'‖ ^ 2 ≤ ⟪u - u', x - x'⟫_ℝ := by
  have h1 := three_point hS hu huK (y := u') (by rwa [norm_sub_rev])
    (EReal.le_coe_toReal hu'.1)
  have h2 := three_point hS hu' hu'K (y := u) hd (EReal.le_coe_toReal hu.1)
  have h4 := norm_sq_four u u' x x'
  rw [norm_sub_rev u' u] at h1
  linarith

/-- Lipschitz bound for proximal points (`2hρ < 1`). -/
theorem prox_lip {f : E → EReal} {K : Set E} {ρ δ h : ℝ} {x x' u u' : E}
    (hS : SemiconvOn f K ρ δ) (hu : IsProxPt f h x u) (hu' : IsProxPt f h x' u')
    (huK : u ∈ K) (hu'K : u' ∈ K) (hd : ‖u - u'‖ ≤ δ) :
    (1 - 2 * h * ρ) * ‖u - u'‖ ≤ ‖x - x'‖ := by
  have h1 := prox_inner_le hS hu hu' huK hu'K hd
  have h2 : ⟪u - u', x - x'⟫_ℝ ≤ ‖u - u'‖ * ‖x - x'‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (u - u')).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have : ‖u - u'‖ * ((1 - 2 * h * ρ) * ‖u - u'‖) ≤ ‖u - u'‖ * ‖x - x'‖ := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- Energy decrease of a proximal step. -/
theorem prox_energy {f : E → EReal} {h : ℝ} {x u : E} {b : ℝ}
    (hu : IsProxPt f h x u) (hb : f x ≤ b) :
    h * (f u).toReal + ‖u - x‖ ^ 2 / 2 ≤ h * b := by
  have := hu.2.2 x b hb
  simpa using this

/-- First-step bound from a local subgradient inequality at `x`. -/
theorem prox_first_step {f : E → EReal} {K : Set E} {ρ δ h : ℝ} {x u w : E}
    (hS : SemiconvOn f K ρ δ) (hu : IsProxPt f h x u) (huK : u ∈ K) (hux : ‖u - x‖ ≤ δ)
    (hh : 0 ≤ h) (hfx : f x ≠ ⊤) (hfx' : f x ≠ ⊥)
    (hw : ∀ y, ‖y - x‖ ≤ δ →
      ((((f x).toReal + ⟪w, y - x⟫_ℝ - ρ * ‖y - x‖ ^ 2 : ℝ)) : EReal) ≤ f y) :
    (1 - 2 * h * ρ) * ‖u - x‖ ≤ h * ‖w‖ := by
  have h1 := three_point hS hu huK (y := x) (by rwa [norm_sub_rev])
    (EReal.le_coe_toReal hfx)
  have h2 := hw u hux
  rw [← EReal.coe_toReal hu.1 hu.2.1, EReal.coe_le_coe_iff] at h2
  rw [norm_sub_rev x u, sub_self, norm_zero] at h1
  have h3 : ⟪w, u - x⟫_ℝ ≥ -(‖w‖ * ‖u - x‖) := by
    have := abs_real_inner_le_norm w (u - x)
    linarith [neg_abs_le ⟪w, u - x⟫_ℝ]
  have h5 : (1 - 2 * h * ρ) * ‖u - x‖ ^ 2 ≤ h * ‖w‖ * ‖u - x‖ := by nlinarith
  rcases (norm_nonneg (u - x)).eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  · have : ‖u - x‖ * ((1 - 2 * h * ρ) * ‖u - x‖) ≤ ‖u - x‖ * (h * ‖w‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- Local proximal subgradient inequality (strict radius). -/
def LocSubgrad (f : E → EReal) (x v : E) (ρ δ : ℝ) : Prop :=
  f x ≠ ⊤ ∧ ∀ y : E, ‖y - x‖ < δ →
    f x + ((⟪v, y - x⟫_ℝ - ρ * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y

theorem LocSubgrad.isRegularSubgrad {f : E → EReal} {x v : E} {ρ δ : ℝ}
    (h : LocSubgrad f x v ρ δ) (hρ : 0 ≤ ρ) (hδ : 0 < δ) : IsRegularSubgrad f x v := by
  refine ⟨h.1, fun ε hε => ?_⟩
  have hη : 0 < min δ (ε / (ρ + 1)) := lt_min hδ (div_pos hε (by linarith))
  filter_upwards [Metric.ball_mem_nhds x hη] with z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hz1 : ‖z - x‖ < δ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : ‖z - x‖ < ε / (ρ + 1) := lt_of_lt_of_le hz (min_le_right _ _)
  refine le_trans ?_ (h.2 z hz1)
  have h3 : ρ * ‖z - x‖ ≤ ε := by
    have : ρ * ‖z - x‖ ≤ (ρ + 1) * ‖z - x‖ := by nlinarith [norm_nonneg (z - x)]
    have h4 : (ρ + 1) * ‖z - x‖ ≤ ε := by
      rw [lt_div_iff₀ (by linarith)] at hz2; linarith
    linarith
  have h5 : ⟪v, z - x⟫_ℝ - ε * ‖z - x‖ ≤ ⟪v, z - x⟫_ℝ - ρ * ‖z - x‖ ^ 2 := by
    nlinarith [norm_nonneg (z - x)]
  exact add_le_add_right (EReal.coe_le_coe_iff.2 h5) _

theorem IsRegularSubgrad.mem_limitingSubdiff {f : E → EReal} {x v : E}
    (h : IsRegularSubgrad f x v) : v ∈ LimitingSubdiff f x :=
  ⟨h.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds,
    fun _ => h⟩

/-- A regular subgradient at a point of `K` satisfies the local proximal inequality. -/
theorem regular_locSubgrad {f : E → EReal} {K : Set E} {ρ δ : ℝ} {u v : E}
    (hS : SemiconvOn f K ρ δ) (hρ : 0 ≤ ρ) (hbot : ∀ z, f z ≠ ⊥) (huK : u ∈ K) (hv : IsRegularSubgrad f u v) :
    ∀ y : E, ‖y - u‖ ≤ δ → f u + ((⟪v, y - u⟫_ℝ - ρ * ‖y - u‖ ^ 2 : ℝ) : EReal) ≤ f y := by
  intro y hy
  by_cases hyt : f y = ⊤
  · rw [hyt]; exact le_top
  set a := (f u).toReal with hadef
  set b := (f y).toReal with hbdef
  have ha : f u = (a : EReal) := (EReal.coe_toReal hv.1 (hbot u)).symm
  have hb : f y = (b : EReal) := (EReal.coe_toReal hyt (hbot y)).symm
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  set d := ‖y - u‖
  -- for every ε > 0: ⟪v, y-u⟫ - ε d ≤ b - a + ρ d²
  have key : ∀ ε : ℝ, 0 < ε → ⟪v, y - u⟫_ℝ - ε * d ≤ b - a + ρ * d ^ 2 := by
    intro ε hε
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 (hv.2 ε hε)
    set θ := min 1 (η / (2 * (d + 1))) with hθdef
    have hθpos : 0 < θ := lt_min one_pos (div_pos hη (by positivity))
    have hθ1 : θ ≤ 1 := min_le_left _ _
    have hθ2 : θ ≤ η / (2 * (d + 1)) := min_le_right _ _
    have hdist : dist (u + θ • (y - u)) u < η := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hθpos.le]
      have : θ * d ≤ η / (2 * (d + 1)) * d := mul_le_mul_of_nonneg_right hθ2 (norm_nonneg _)
      have h5 : η / (2 * (d + 1)) * d < η := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (y - u)]
      linarith
    have h1 := hball hdist
    have h2 := hS u huK y hy θ hθpos.le hθ1 a b ha.le hb.le
    rw [ha] at h1
    have h3 := h1.trans h2
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, add_sub_cancel_left, inner_smul_right,
      norm_smul, Real.norm_of_nonneg hθpos.le] at h3
    have h4 : θ * (⟪v, y - u⟫_ℝ - ε * d) ≤ θ * (b - a + ρ * d ^ 2) := by
      have : 0 ≤ ρ * θ * θ * d ^ 2 := by positivity
      nlinarith
    exact le_of_mul_le_mul_left h4 hθpos
  by_contra hcon
  push Not at hcon
  have hd1 : 0 < d + 1 := by positivity
  have := key ((a + ⟪v, y - u⟫_ℝ - ρ * d ^ 2 - b) / (2 * (d + 1))) (div_pos (by linarith) (by positivity))
  have h7 : (a + ⟪v, y - u⟫_ℝ - ρ * d ^ 2 - b) / (2 * (d + 1)) * d
      ≤ (a + ⟪v, y - u⟫_ℝ - ρ * d ^ 2 - b) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg (y - u)]
  linarith

/-- Limiting subgradients at points well inside a ball of semiconvexity are local proximal
subgradients. -/
theorem limiting_locSubgrad {f : E → EReal} {R ρ δ : ℝ} {a v : E}
    (hS : SemiconvOn f (Metric.closedBall 0 R) ρ δ) (hρ : 0 ≤ ρ) (hbot : ∀ z, f z ≠ ⊥) (ha : ‖a‖ < R)
    (hv : v ∈ LimitingSubdiff f a) : LocSubgrad f a v ρ δ := by
  obtain ⟨hat, xs, vs, hxs, hfxs, hvs, hreg⟩ := hv
  refine ⟨hat, fun y hy => ?_⟩
  have hK : ∀ᶠ k in atTop, xs k ∈ Metric.closedBall (0 : E) R := by
    have : Metric.ball (0 : E) R ∈ 𝓝 a := Metric.isOpen_ball.mem_nhds (by simpa using ha)
    filter_upwards [hxs this] with k hk using Metric.ball_subset_closedBall hk
  have hδ' : ∀ᶠ k in atTop, ‖y - xs k‖ < δ := by
    have hc : Tendsto (fun k => ‖y - xs k‖) atTop (𝓝 ‖y - a‖) :=
      (tendsto_const_nhds.sub hxs).norm
    exact hc.eventually (gt_mem_nhds hy)
  have hlim : Tendsto (fun k => f (xs k) + ((⟪vs k, y - xs k⟫_ℝ - ρ * ‖y - xs k‖ ^ 2 : ℝ) : EReal))
      atTop (𝓝 (f a + ((⟪v, y - a⟫_ℝ - ρ * ‖y - a‖ ^ 2 : ℝ) : EReal))) := by
    have hr : Tendsto (fun k => ((⟪vs k, y - xs k⟫_ℝ - ρ * ‖y - xs k‖ ^ 2 : ℝ) : EReal)) atTop
        (𝓝 ((⟪v, y - a⟫_ℝ - ρ * ‖y - a‖ ^ 2 : ℝ) : EReal)) := by
      apply (EReal.continuous_coe_iff.2 continuous_id).continuousAt.tendsto.comp
      exact (hvs.inner (tendsto_const_nhds.sub hxs)).sub
        (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hxs).norm.pow 2))
    exact (EReal.continuousAt_add (Or.inl hat) (Or.inr (EReal.coe_ne_top _))).tendsto.comp
      (hfxs.prodMk_nhds hr)
  refine le_of_tendsto hlim ?_
  filter_upwards [hK, hδ'] with k hk hk'
  exact regular_locSubgrad hS hρ hbot hk (hreg k) y hk'.le

/-- Existence of a proximal point (finite dimension, lsc, bounded below, proper). -/
theorem exists_proxPt [FiniteDimensional ℝ E] {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hbot : ∀ z, f z ≠ ⊥) {m : ℝ} (hm : ∀ z, (m : EReal) ≤ f z) {y0 : E} (hy0 : f y0 ≠ ⊤)
    {h : ℝ} (hh : 0 < h) (x : E) : ∃ u, IsProxPt f h x u := by
  set g : E → EReal := fun v => f v + ((‖v - x‖ ^ 2 / (2 * h) : ℝ) : EReal) with hg
  have hglsc : LowerSemicontinuous g := by
    refine LowerSemicontinuous.add' hlsc ?_ ?_
    · exact (EReal.continuous_coe_iff.2
        (((continuous_id.sub continuous_const).norm.pow 2).div_const _)).lowerSemicontinuous
    · intro z
      exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  set c : ℝ := (f y0).toReal + ‖y0 - x‖ ^ 2 / (2 * h) with hcdef
  have hgy0 : g y0 = (c : EReal) := by
    simp only [hg, hcdef, EReal.coe_add, EReal.coe_toReal hy0 (hbot y0)]
  set R : ℝ := |2 * h * (c - m)| + 1 + ‖y0 - x‖ with hRdef
  have hy0B : y0 ∈ Metric.closedBall x R := by
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith [abs_nonneg (2 * h * (c - m))]
  obtain ⟨u, -, humin⟩ :=
    (hglsc.lowerSemicontinuousOn _).exists_isMinOn ⟨y0, hy0B⟩ (isCompact_closedBall x R)
  have hgu : g u ≤ c := hgy0 ▸ humin hy0B
  have hglob : ∀ v, g u ≤ g v := by
    intro v
    by_cases hv : v ∈ Metric.closedBall x R
    · exact humin hv
    · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hv
      have h0 : 1 ≤ ‖v - x‖ := by linarith [abs_nonneg (2 * h * (c - m)), norm_nonneg (y0 - x)]
      have h1 : (c - m) * (2 * h) ≤ ‖v - x‖ ^ 2 := by
        nlinarith [le_abs_self (2 * h * (c - m)), norm_nonneg (y0 - x)]
      have h2 : c ≤ m + ‖v - x‖ ^ 2 / (2 * h) := by
        have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * h)).2 h1
        linarith
      refine hgu.trans ?_
      calc ((c : ℝ) : EReal) ≤ ((m + ‖v - x‖ ^ 2 / (2 * h) : ℝ) : EReal) := EReal.coe_le_coe h2
        _ = (m : EReal) + ((‖v - x‖ ^ 2 / (2 * h) : ℝ) : EReal) := EReal.coe_add _ _
        _ ≤ g v := add_le_add_left (hm v) _
  have hut : f u ≠ ⊤ := by
    intro htop
    have : g u = ⊤ := by simp only [hg, htop, EReal.top_add_coe]
    rw [this] at hgu
    exact EReal.coe_ne_top _ (top_le_iff.1 hgu)
  refine ⟨u, hut, hbot u, fun v b hb => ?_⟩
  have h3 := (hglob v).trans (add_le_add_left hb _)
  simp only [hg] at h3
  rw [← EReal.coe_toReal hut (hbot u), ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h3
  have h4 := mul_le_mul_of_nonneg_left h3 hh.le
  have e1 : h * ((f u).toReal + ‖u - x‖ ^ 2 / (2 * h)) = h * (f u).toReal + ‖u - x‖ ^ 2 / 2 := by
    field_simp
  have e2 : h * (b + ‖v - x‖ ^ 2 / (2 * h)) = h * b + ‖v - x‖ ^ 2 / 2 := by
    field_simp
  linarith


/-! ## L3: the minimizing-movement scheme (abstract sequence of proximal steps) -/

noncomputable def Fv (f : E → EReal) (X : ℕ → E) (j : ℕ) : ℝ := (f (X j)).toReal

/-- A sequence of proximal steps of size `h` starting at a point of finite value. -/
structure IsScheme (f : E → EReal) (h : ℝ) (X : ℕ → E) : Prop where
  pos : 0 < h
  bot : ∀ z, f z ≠ ⊥
  fin0 : f (X 0) ≠ ⊤
  step : ∀ j, IsProxPt f h (X j) (X (j + 1))

section Scheme

variable {f : E → EReal} {h : ℝ} {X : ℕ → E}

lemma IsScheme.fin (hX : IsScheme f h X) (j : ℕ) : f (X j) ≠ ⊤ := by
  cases j with
  | zero => exact hX.fin0
  | succ j => exact (hX.step j).1

lemma IsScheme.coe (hX : IsScheme f h X) (j : ℕ) : f (X j) = ((Fv f X j : ℝ) : EReal) :=
  (EReal.coe_toReal (hX.fin j) (hX.bot _)).symm

lemma IsScheme.energy (hX : IsScheme f h X) (j : ℕ) :
    h * Fv f X (j + 1) + ‖X (j + 1) - X j‖ ^ 2 / 2 ≤ h * Fv f X j :=
  prox_energy (hX.step j) (hX.coe j).le

lemma IsScheme.F_succ_le (hX : IsScheme f h X) (j : ℕ) : Fv f X (j + 1) ≤ Fv f X j := by
  have h1 := hX.energy j
  have h2 : h * Fv f X (j + 1) ≤ h * Fv f X j := by
    nlinarith [sq_nonneg ‖X (j + 1) - X j‖]
  exact le_of_mul_le_mul_left h2 hX.pos

lemma IsScheme.F_anti (hX : IsScheme f h X) : Antitone (Fv f X) :=
  antitone_nat_of_succ_le hX.F_succ_le

lemma IsScheme.sum_sq (hX : IsScheme f h X) (j : ℕ) :
    ∑ i ∈ Finset.range j, ‖X (i + 1) - X i‖ ^ 2 ≤ 2 * h * (Fv f X 0 - Fv f X j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ]; have := hX.energy j; linarith

lemma IsScheme.F_ge (hX : IsScheme f h X) {m : ℝ} (hm : ∀ z, (m : EReal) ≤ f z) (j : ℕ) :
    m ≤ Fv f X j := by
  have := hm (X j); rw [hX.coe j] at this; exact EReal.coe_le_coe_iff.1 this

lemma IsScheme.step_sq (hX : IsScheme f h X) {m : ℝ} (hm : ∀ z, (m : EReal) ≤ f z) (j : ℕ) :
    ‖X (j + 1) - X j‖ ^ 2 ≤ 2 * h * (Fv f X 0 - m) := by
  have h1 := hX.energy j
  have h2 := mul_le_mul_of_nonneg_left (hX.F_anti (Nat.zero_le j)) hX.pos.le
  have h3 := mul_le_mul_of_nonneg_left (hX.F_ge hm (j + 1)) hX.pos.le
  linarith

lemma IsScheme.dist_sq (hX : IsScheme f h X) {m : ℝ} (hm : ∀ z, (m : EReal) ≤ f z) (j : ℕ) :
    ‖X j - X 0‖ ^ 2 ≤ 2 * (j * h) * (Fv f X 0 - m) := by
  have htel : X j - X 0 = ∑ i ∈ Finset.range j, (X (i + 1) - X i) :=
    (Finset.sum_range_sub X j).symm
  have h1 : ‖X j - X 0‖ ≤ ∑ i ∈ Finset.range j, ‖X (i + 1) - X i‖ := htel ▸ norm_sum_le _ _
  have h2 : (∑ i ∈ Finset.range j, ‖X (i + 1) - X i‖) ^ 2
      ≤ j * ∑ i ∈ Finset.range j, ‖X (i + 1) - X i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range j) (f := fun i => ‖X (i + 1) - X i‖)
    simpa using this
  have h3 := hX.sum_sq j
  have h4 := hX.F_ge hm j
  have h5 : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hX.pos.le
  calc ‖X j - X 0‖ ^ 2 ≤ (∑ i ∈ Finset.range j, ‖X (i + 1) - X i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ j * ∑ i ∈ Finset.range j, ‖X (i + 1) - X i‖ ^ 2 := h2
    _ ≤ j * (2 * h * (Fv f X 0 - Fv f X j)) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg j)
    _ ≤ 2 * (j * h) * (Fv f X 0 - m) := by nlinarith

/-- One-step contraction of the speed. -/
lemma IsScheme.speed_step (hX : IsScheme f h X) {K : Set E} {ρ δ : ℝ} (hS : SemiconvOn f K ρ δ)
    {M : ℕ} (hK : ∀ i ≤ M, X i ∈ K) (hδ : ∀ i < M, ‖X (i + 1) - X i‖ ≤ δ) {j : ℕ}
    (hj : j + 2 ≤ M) :
    (1 - 2 * h * ρ) * ‖X (j + 2) - X (j + 1)‖ ≤ ‖X (j + 1) - X j‖ :=
  prox_lip hS (hX.step (j + 1)) (hX.step j) (hK _ hj) (hK _ (by omega)) (hδ (j + 1) (by omega))

lemma locSubgrad_real {f : E → EReal} {x w : E} {ρ δ δ' : ℝ} (hw : LocSubgrad f x w ρ δ')
    (hbot : f x ≠ ⊥) (hδ : δ < δ') :
    ∀ y, ‖y - x‖ ≤ δ →
      ((((f x).toReal + ⟪w, y - x⟫_ℝ - ρ * ‖y - x‖ ^ 2 : ℝ)) : EReal) ≤ f y := by
  intro y hy
  have := hw.2 y (lt_of_le_of_lt hy hδ)
  rw [← EReal.coe_toReal hw.1 hbot, ← EReal.coe_add] at this
  simpa [add_sub_assoc] using this

/-- Speed bound `q^(j+1) ‖Δ_j‖ ≤ h ‖w‖`, `q = 1 - 2hρ`. -/
lemma IsScheme.speed_pow (hX : IsScheme f h X) {K : Set E} {ρ δ δ' : ℝ}
    (hS : SemiconvOn f K ρ δ) {M : ℕ} (hK : ∀ i ≤ M, X i ∈ K)
    (hδ : ∀ i < M, ‖X (i + 1) - X i‖ ≤ δ) {w : E} (hw : LocSubgrad f (X 0) w ρ δ')
    (hδδ : δ < δ') (hq : 0 ≤ 1 - 2 * h * ρ) :
    ∀ j, j + 1 ≤ M → (1 - 2 * h * ρ) ^ (j + 1) * ‖X (j + 1) - X j‖ ≤ h * ‖w‖ := by
  intro j
  induction j with
  | zero =>
    intro hM
    simpa using prox_first_step hS (hX.step 0) (hK 1 hM) (hδ 0 (by omega)) hX.pos.le hX.fin0
      (hX.bot _) (locSubgrad_real hw (hX.bot _) hδδ)
  | succ j ih =>
    intro hM
    have h1 := hX.speed_step hS hK hδ (j := j) (by omega)
    have h2 := ih (by omega)
    calc (1 - 2 * h * ρ) ^ (j + 1 + 1) * ‖X (j + 1 + 1) - X (j + 1)‖
        = (1 - 2 * h * ρ) ^ (j + 1) * ((1 - 2 * h * ρ) * ‖X (j + 2) - X (j + 1)‖) := by ring
      _ ≤ (1 - 2 * h * ρ) ^ (j + 1) * ‖X (j + 1) - X j‖ :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg hq _)
      _ ≤ h * ‖w‖ := h2

lemma pow_mul_exp_ge {a : ℝ} (ha : 0 ≤ a) (ha4 : 4 * a ≤ 1) (n : ℕ) :
    1 ≤ (1 - 2 * a) ^ n * Real.exp (4 * a * n) := by
  have h1 : 1 ≤ (1 - 2 * a) * Real.exp (4 * a) := by
    have h0 := Real.add_one_le_exp (4 * a)
    have h2 : 0 ≤ 1 - 2 * a := by linarith
    have h5 := mul_le_mul_of_nonneg_left h0 h2
    nlinarith [mul_nonneg ha (by linarith : (0:ℝ) ≤ 1 - 4 * a)]
  have h3 : Real.exp (4 * a * n) = Real.exp (4 * a) ^ n := by
    rw [mul_comm (4 * a) _, Real.exp_nat_mul]
  rw [h3, ← mul_pow]
  exact one_le_pow₀ h1

/-- Exponential speed bound on the scheme. -/
lemma IsScheme.speed_le (hX : IsScheme f h X) {K : Set E} {ρ δ δ' : ℝ}
    (hS : SemiconvOn f K ρ δ) {M : ℕ} (hK : ∀ i ≤ M, X i ∈ K)
    (hδ : ∀ i < M, ‖X (i + 1) - X i‖ ≤ δ) {w : E} (hw : LocSubgrad f (X 0) w ρ δ')
    (hδδ : δ < δ') (hρ : 0 ≤ ρ) (h4 : 4 * h * ρ ≤ 1) :
    ∀ j, j + 1 ≤ M →
      ‖X (j + 1) - X j‖ ≤ h * ‖w‖ * Real.exp (4 * ρ * (h * ((j : ℝ) + 1))) := by
  intro j hj
  have hq : 0 ≤ 1 - 2 * h * ρ := by nlinarith [hX.pos]
  have h1 := hX.speed_pow hS hK hδ hw hδδ hq j hj
  have h2 := pow_mul_exp_ge (a := h * ρ) (mul_nonneg hX.pos.le hρ) (by linarith) (j + 1)
  have e1 : (1 - 2 * (h * ρ)) = 1 - 2 * h * ρ := by ring
  have e2 : Real.exp (4 * (h * ρ) * ((j + 1 : ℕ) : ℝ)) = Real.exp (4 * ρ * (h * ((j : ℝ) + 1))) := by
    congr 1; push_cast; ring
  rw [e1, e2] at h2
  set s := ‖X (j + 1) - X j‖
  set Q := (1 - 2 * h * ρ) ^ (j + 1)
  set G := Real.exp (4 * ρ * (h * ((j : ℝ) + 1)))
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hs : 0 ≤ s := norm_nonneg _
  calc s = s * 1 := (mul_one s).symm
    _ ≤ s * (Q * G) := mul_le_mul_of_nonneg_left h2 hs
    _ = (Q * s) * G := by ring
    _ ≤ (h * ‖w‖) * G := mul_le_mul_of_nonneg_right h1 hG

/-- Grid Lipschitz bound from a uniform step bound. -/
lemma grid_lip {X : ℕ → E} {c : ℝ} {j : ℕ} :
    ∀ d : ℕ, (∀ i, j ≤ i → i < j + d → ‖X (i + 1) - X i‖ ≤ c) → ‖X (j + d) - X j‖ ≤ d * c := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hs
    have h1 := ih (fun i hi1 hi2 => hs i hi1 (by omega))
    have h2 := hs (j + d) (by omega) (by omega)
    calc ‖X (j + (d + 1)) - X j‖ ≤ ‖X (j + d + 1) - X (j + d)‖ + ‖X (j + d) - X j‖ := by
          rw [← add_assoc]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ c + d * c := add_le_add h2 h1
      _ = ((d + 1 : ℕ) : ℝ) * c := by push_cast; ring

/-- Discrete local evolution variational inequality. -/
lemma IsScheme.levi (hX : IsScheme f h X) {K : Set E} {ρ δ : ℝ} (hS : SemiconvOn f K ρ δ)
    (hρ : 0 ≤ ρ) {j m : ℕ} (hjm : j ≤ m) {y : E} {b r : ℝ} (hb : f y ≤ b)
    (hK : ∀ i, j < i → i ≤ m → X i ∈ K) (hr : ∀ i, j < i → i ≤ m → ‖y - X i‖ ≤ r)
    (hrδ : r ≤ δ) :
    ‖y - X m‖ ^ 2 / 2 - ‖y - X j‖ ^ 2 / 2
      ≤ (((m - j : ℕ) : ℝ) * h) * (b - Fv f X m) + ρ * ((((m - j : ℕ) : ℝ) * h) * r ^ 2) := by
  suffices H : ∀ d : ℕ, j + d ≤ m → ‖y - X (j + d)‖ ^ 2 / 2 - ‖y - X j‖ ^ 2 / 2
      ≤ ((d : ℝ) * h) * (b - Fv f X m) + ρ * (((d : ℝ) * h) * r ^ 2) by
    have := H (m - j) (by omega)
    rwa [show j + (m - j) = m by omega] at this
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have hi1 : j < j + d + 1 := by omega
    have hi2 : j + d + 1 ≤ m := by omega
    have hry := hr _ hi1 hi2
    have h2 := three_point hS (hX.step (j + d)) (hK _ hi1 hi2) (hry.trans hrδ) hb
    have h3 := hX.F_anti hi2
    have h4 : ‖y - X (j + d + 1)‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hry 2
    have h5 : h * ρ * ‖y - X (j + d + 1)‖ ^ 2 ≤ h * ρ * r ^ 2 :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hX.pos.le hρ)
    have h6 : h * Fv f X m ≤ h * Fv f X (j + d + 1) := mul_le_mul_of_nonneg_left h3 hX.pos.le
    have h7 : 0 ≤ ‖X (j + d + 1) - X (j + d)‖ ^ 2 := sq_nonneg _
    rw [show j + (d + 1) = j + d + 1 by omega]
    push_cast
    unfold Fv at *
    nlinarith

end Scheme


/-! ## L4: compactness (diagonal subsequence on dyadic times, extension to all times) -/

theorem diag_subseq [ProperSpace E] (a : ℕ → ℕ × ℕ → E) (c : E) (r : ℕ × ℕ → ℝ)
    (ha : ∀ k p, ‖a k p - c‖ ≤ r p) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ p, ∃ A : E, Tendsto (fun i => a (φ i) p) atTop (𝓝 A) := by
  have hs : IsCompact (Set.pi Set.univ fun p : ℕ × ℕ => Metric.closedBall c (r p)) :=
    isCompact_univ_pi fun p => isCompact_closedBall c (r p)
  obtain ⟨A, -, φ, hφ, hlim⟩ := hs.tendsto_subseq (x := a) (fun k => Set.mem_univ_pi.2
    (fun p => by rw [Metric.mem_closedBall, dist_eq_norm]; exact ha k p))
  exact ⟨φ, hφ, fun p => ⟨A p, (continuous_apply p).continuousAt.tendsto.comp hlim⟩⟩

theorem conv_all [CompleteSpace E] (g : ℕ → ℝ → E) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hdy : ∀ l j : ℕ, ∃ A : E, Tendsto (fun i => g (φ i) ((j : ℝ) / 2 ^ l)) atTop (𝓝 A))
    (hmod : ∀ t : ℝ, 0 ≤ t → ∃ L : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ s : ℝ, 0 ≤ s → s ≤ t →
      ‖g k t - g k s‖ ≤ L * (t - s + (1 / 2) ^ k)) :
    ∀ t : ℝ, 0 ≤ t → ∃ A : E, Tendsto (fun i => g (φ i) t) atTop (𝓝 A) := by
  intro t ht
  obtain ⟨L, k0, hL⟩ := hmod t ht
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set L' := |L| + 1 with hL'
  have hL'pos : 0 < L' := by positivity
  obtain ⟨l, hl⟩ := exists_pow_lt_of_lt_one (div_pos hε (by positivity : (0:ℝ) < 8 * L'))
    (by norm_num : (1 / 2 : ℝ) < 1)
  set j := ⌊t * 2 ^ l⌋₊ with hj
  set d : ℝ := (j : ℝ) / 2 ^ l with hd
  have h2l : (0 : ℝ) < 2 ^ l := by positivity
  have hd0 : 0 ≤ d := by positivity
  have hdt : d ≤ t := by
    rw [hd, div_le_iff₀ h2l]; exact Nat.floor_le (by positivity)
  have htd : t - d ≤ (1 / 2) ^ l := by
    have h1 : t * 2 ^ l < j + 1 := Nat.lt_floor_add_one _
    have h3 : t < (j + 1) / 2 ^ l := by rw [lt_div_iff₀ h2l]; exact h1
    have h4 : ((j : ℝ) + 1) / 2 ^ l = d + (1 / 2) ^ l := by
      rw [hd, one_div_pow, add_div, one_div]
    linarith
  obtain ⟨A, hA⟩ := hdy l j
  obtain ⟨I1, hI1⟩ := Metric.cauchySeq_iff.1 hA.cauchySeq (ε / 4) (by positivity)
  have hclose : ∀ i ≥ max I1 (max k0 l), dist (g (φ i) t) (g (φ i) d) < ε / 4 := by
    intro i hi
    have hi0 : k0 ≤ φ i := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans hi (hφ.id_le i))
    have hil : l ≤ φ i := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans hi (hφ.id_le i))
    have hpow : (1 / 2 : ℝ) ^ φ i ≤ (1 / 2) ^ l := pow_le_pow_of_le_one (by norm_num) (by norm_num) hil
    rw [dist_eq_norm]
    have h1 := hL (φ i) hi0 d hd0 hdt
    have h5 : 0 ≤ t - d + (1 / 2) ^ φ i := by have := pow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) (φ i); linarith
    have h6 : L * (t - d + (1 / 2) ^ φ i) ≤ L' * (t - d + (1 / 2) ^ φ i) :=
      mul_le_mul_of_nonneg_right (by rw [hL']; linarith [le_abs_self L]) h5
    have h7 : L' * (t - d + (1 / 2) ^ φ i) ≤ L' * (2 * (1 / 2) ^ l) :=
      mul_le_mul_of_nonneg_left (by linarith) hL'pos.le
    have h8 : L' * (2 * (1 / 2) ^ l) < ε / 4 := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 8 * L')] at hl
      nlinarith
    linarith
  refine ⟨max I1 (max k0 l), fun i hi i' hi' => ?_⟩
  have e1 := hclose i hi
  have e2 := hclose i' hi'
  have e3 := hI1 i (le_trans (le_max_left _ _) hi) i' (le_trans (le_max_left _ _) hi')
  calc dist (g (φ i) t) (g (φ i') t)
      ≤ dist (g (φ i) t) (g (φ i) d) + dist (g (φ i) d) (g (φ i') d) + dist (g (φ i') d) (g (φ i') t) :=
        dist_triangle4 _ _ _ _
    _ < ε / 4 + ε / 4 + ε / 4 := by rw [dist_comm (g (φ i') d)]; linarith
    _ < ε := by linarith


/-! ## L5a: dyadic minimizing-movement schemes for a good function -/

/-- Standing hypothesis (H): lsc, never `⊥`, bounded below by `m`, uniformly locally semiconvex
on bounded sets. -/
structure GoodF (f : E → EReal) (m : ℝ) : Prop where
  lsc : LowerSemicontinuous f
  bot : ∀ z, f z ≠ ⊥
  lb : ∀ z, (m : EReal) ≤ f z
  semi : ∀ R : ℝ, ∃ ρ δ : ℝ, 0 ≤ ρ ∧ 0 < δ ∧ SemiconvOn f (Metric.closedBall 0 R) ρ δ

lemma SemiconvOn.mono_delta {f : E → EReal} {K : Set E} {ρ δ δ' : ℝ} (h : SemiconvOn f K ρ δ)
    (hδ : δ' ≤ δ) : SemiconvOn f K ρ δ' :=
  fun u hu y hy θ h0 h1 a b ha hb => h u hu y (hy.trans hδ) θ h0 h1 a b ha hb

section Construction

variable [FiniteDimensional ℝ E] {f : E → EReal} {m : ℝ} {x0 : E}

noncomputable def proxMap (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (h : ℝ) (x : E) : E :=
  if hh : 0 < h then Classical.choose (exists_proxPt hf.lsc hf.bot hf.lb hx0 hh x) else x

lemma proxMap_spec (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) {h : ℝ} (hh : 0 < h) (x : E) :
    IsProxPt f h x (proxMap hf hx0 h x) := by
  unfold proxMap; rw [dif_pos hh]; exact Classical.choose_spec _

noncomputable def schemeX (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k j : ℕ) : E :=
  (proxMap hf hx0 ((1 / 2 : ℝ) ^ k))^[j] x0

lemma schemeX_zero (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) : schemeX hf hx0 k 0 = x0 := rfl

lemma schemeX_isScheme (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) :
    IsScheme f ((1 / 2 : ℝ) ^ k) (schemeX hf hx0 k) where
  pos := by positivity
  bot := hf.bot
  fin0 := hx0
  step j := by
    simp only [schemeX, Function.iterate_succ_apply']
    exact proxMap_spec hf hx0 (by positivity) _

/-- Piecewise-constant interpolation of the `k`-th scheme. -/
noncomputable def gpath (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) (t : ℝ) : E :=
  schemeX hf hx0 k ⌊t / (1 / 2 : ℝ) ^ k⌋₊

lemma Fv_zero (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) :
    Fv f (schemeX hf hx0 k) 0 = (f x0).toReal := rfl

/-- Per-horizon constants. -/
theorem consts (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) {w : E} (hw : w ∈ LimitingSubdiff f x0)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ R ρ δ L : ℝ, ∃ k0 : ℕ, 0 ≤ ρ ∧ 0 < δ ∧ 0 ≤ L ∧
      SemiconvOn f (Metric.closedBall 0 R) ρ δ ∧ ‖x0‖ ≤ R - 1 ∧
      ∀ k ≥ k0, 4 * (1 / 2 : ℝ) ^ k * ρ ≤ 1 ∧
        (∀ i : ℕ, (i : ℝ) * (1 / 2 : ℝ) ^ k ≤ T + 1 → ‖schemeX hf hx0 k i‖ ≤ R - 1) ∧
        (∀ i : ℕ, ‖schemeX hf hx0 k (i + 1) - schemeX hf hx0 k i‖ ≤ δ / 2) ∧
        (∀ i : ℕ, ((i : ℝ) + 1) * (1 / 2 : ℝ) ^ k ≤ T + 1 →
          ‖schemeX hf hx0 k (i + 1) - schemeX hf hx0 k i‖ ≤ (1 / 2 : ℝ) ^ k * L) := by
  set f0 := (f x0).toReal with hf0
  have hf0m : m ≤ f0 := by
    have := hf.lb x0
    rw [← EReal.coe_toReal hx0 (hf.bot x0), EReal.coe_le_coe_iff] at this
    exact this
  set R := ‖x0‖ + Real.sqrt (2 * (T + 1) * (f0 - m)) + 1 with hR
  obtain ⟨ρ, δ, hρ, hδ, hS⟩ := hf.semi R
  have hx0R : ‖x0‖ < R := by have := Real.sqrt_nonneg (2 * (T + 1) * (f0 - m)); linarith
  have hw' : LocSubgrad f x0 w ρ δ := limiting_locSubgrad hS hρ hf.bot hx0R hw
  set L := ‖w‖ * Real.exp (4 * ρ * (T + 1)) with hL
  set η := min (1 / (4 * ρ + 1)) (min (δ ^ 2 / (8 * (f0 - m) + 1)) 1) with hη
  have hηpos : 0 < η := lt_min (by positivity) (lt_min (by positivity) one_pos)
  obtain ⟨k0, hk0⟩ := exists_pow_lt_of_lt_one hηpos (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨R, ρ, δ, L, k0, hρ, hδ, by positivity, hS,
    by have := Real.sqrt_nonneg (2 * (T + 1) * (f0 - m)); linarith, fun k hk => ?_⟩
  set h := (1 / 2 : ℝ) ^ k with hh
  have hhpos : 0 < h := by positivity
  have hhη : h < η := lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hk0
  have hh1 : h ≤ 1 / (4 * ρ + 1) := le_trans hhη.le (min_le_left _ _)
  have hh2 : h ≤ δ ^ 2 / (8 * (f0 - m) + 1) :=
    le_trans hhη.le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hX := schemeX_isScheme hf hx0 k
  have h4 : 4 * h * ρ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hh1; nlinarith
  have hball : ∀ i : ℕ, (i : ℝ) * h ≤ T + 1 → ‖schemeX hf hx0 k i‖ ≤ R - 1 := by
    intro i hi
    have h1 := hX.dist_sq hf.lb i
    rw [Fv_zero] at h1
    have h2 : ‖schemeX hf hx0 k i - x0‖ ^ 2 ≤ 2 * (T + 1) * (f0 - m) := by
      have : 2 * ((i : ℝ) * h) * (f0 - m) ≤ 2 * (T + 1) * (f0 - m) := by
        have := sub_nonneg.2 hf0m; nlinarith
      exact h1.trans this
    have h3 : ‖schemeX hf hx0 k i - x0‖ ≤ Real.sqrt (2 * (T + 1) * (f0 - m)) :=
      Real.le_sqrt_of_sq_le h2
    have h5 := norm_sub_norm_le (schemeX hf hx0 k i) x0
    linarith
  have hstep : ∀ i : ℕ, ‖schemeX hf hx0 k (i + 1) - schemeX hf hx0 k i‖ ≤ δ / 2 := by
    intro i
    have h1 := hX.step_sq hf.lb i
    rw [Fv_zero] at h1
    have h2 : 2 * h * (f0 - m) ≤ (δ / 2) ^ 2 := by
      rw [le_div_iff₀ (by have := sub_nonneg.2 hf0m; positivity)] at hh2
      have := sub_nonneg.2 hf0m
      nlinarith
    have h3 := h1.trans h2
    nlinarith [norm_nonneg (schemeX hf hx0 k (i + 1) - schemeX hf hx0 k i)]
  refine ⟨h4, hball, hstep, fun i hi => ?_⟩
  have hK : ∀ i' ≤ i + 1, schemeX hf hx0 k i' ∈ Metric.closedBall (0 : E) R := by
    intro i' hi'
    rw [mem_closedBall_zero_iff]
    have : (i' : ℝ) * h ≤ T + 1 := by
      have : (i' : ℝ) ≤ i + 1 := by exact_mod_cast hi'
      nlinarith
    linarith [hball i' this]
  have hδ' : ∀ i' < i + 1, ‖schemeX hf hx0 k (i' + 1) - schemeX hf hx0 k i'‖ ≤ δ / 2 :=
    fun i' _ => hstep i'
  have h1 := hX.speed_le (hS.mono_delta (by linarith : δ / 2 ≤ δ)) hK hδ' (w := w)
    (by rwa [schemeX_zero]) (by linarith : δ / 2 < δ) hρ h4 i le_rfl
  have h2 : Real.exp (4 * ρ * (h * ((i : ℝ) + 1))) ≤ Real.exp (4 * ρ * (T + 1)) := by
    apply Real.exp_le_exp.2
    have : h * ((i : ℝ) + 1) ≤ T + 1 := by linarith
    nlinarith
  calc ‖schemeX hf hx0 k (i + 1) - schemeX hf hx0 k i‖
      ≤ h * ‖w‖ * Real.exp (4 * ρ * (h * ((i : ℝ) + 1))) := h1
    _ ≤ h * ‖w‖ * Real.exp (4 * ρ * (T + 1)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = h * L := by rw [hL]; ring

/-- Asymptotic equicontinuity of the interpolants (input of `conv_all`). -/
theorem gpath_mod (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) {w : E} (hw : w ∈ LimitingSubdiff f x0) :
    ∀ t : ℝ, 0 ≤ t → ∃ L : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ s : ℝ, 0 ≤ s → s ≤ t →
      ‖gpath hf hx0 k t - gpath hf hx0 k s‖ ≤ L * (t - s + (1 / 2) ^ k) := by
  intro t ht
  obtain ⟨R, ρ, δ, L, k0, hρ, hδ, hL, hS, hx0R, hk⟩ := consts hf hx0 hw t ht
  refine ⟨L, k0, fun k hk' s hs hst => ?_⟩
  obtain ⟨-, -, -, hsp⟩ := hk k hk'
  set h := (1 / 2 : ℝ) ^ k with hh
  have hhpos : 0 < h := by positivity
  set a := ⌊s / h⌋₊ with ha
  set b := ⌊t / h⌋₊ with hb
  have hab : a ≤ b := Nat.floor_mono (div_le_div_of_nonneg_right hst hhpos.le)
  have hbt : (b : ℝ) * h ≤ t := (le_div_iff₀ hhpos).1 (Nat.floor_le (div_nonneg ht hhpos.le))
  have has : s < ((a : ℝ) + 1) * h := (div_lt_iff₀ hhpos).1 (Nat.lt_floor_add_one _)
  have hg := grid_lip (X := schemeX hf hx0 k) (c := h * L) (j := a) (b - a) (fun i hi1 hi2 => by
    apply hsp i
    have : ((i : ℝ) + 1) ≤ b := by exact_mod_cast (show i + 1 ≤ b by omega)
    nlinarith)
  rw [show a + (b - a) = b by omega, Nat.cast_sub hab] at hg
  show ‖schemeX hf hx0 k b - schemeX hf hx0 k a‖ ≤ L * (t - s + h)
  refine hg.trans ?_
  have : ((b : ℝ) - a) * h ≤ t - s + h := by nlinarith
  nlinarith

end Construction

/-! ## L5b: the limit curve, its Lipschitz bound and its local EVI -/

section Limit

variable [FiniteDimensional ℝ E] {f : E → EReal} {m : ℝ} {x0 : E}

/-- Grid time `⌊t/h⌋ h` for `h = 2^-k`. -/
noncomputable def gridT (k : ℕ) (t : ℝ) : ℝ := (⌊t / (1 / 2 : ℝ) ^ k⌋₊ : ℝ) * (1 / 2 : ℝ) ^ k

lemma floor_mul_le {t h : ℝ} (ht : 0 ≤ t) (hh : 0 < h) : (⌊t / h⌋₊ : ℝ) * h ≤ t :=
  (le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg ht hh.le))

lemma lt_floor_mul {t h : ℝ} (hh : 0 < h) : t < ((⌊t / h⌋₊ : ℝ) + 1) * h :=
  (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one _)

lemma gridT_mono (k : ℕ) {s t : ℝ} (hst : s ≤ t) : gridT k s ≤ gridT k t := by
  unfold gridT
  have hpos : (0 : ℝ) < (1 / 2) ^ k := by positivity
  exact mul_le_mul_of_nonneg_right
    (Nat.cast_le.2 (Nat.floor_mono (div_le_div_of_nonneg_right hst hpos.le))) hpos.le

lemma tendsto_half_pow {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun i => (1 / 2 : ℝ) ^ (φ i)) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hφ.tendsto_atTop

lemma tendsto_gridT {φ : ℕ → ℕ} (hφ : StrictMono φ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun i => gridT (φ i) t) atTop (𝓝 t) := by
  have hlow : Tendsto (fun i => t - (1 / 2 : ℝ) ^ (φ i)) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub (tendsto_half_pow hφ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun i => ?_) (fun i => ?_)
  · have := lt_floor_mul (t := t) (h := (1 / 2 : ℝ) ^ (φ i)) (by positivity)
    show t - (1 / 2 : ℝ) ^ (φ i) ≤ (⌊t / (1 / 2 : ℝ) ^ (φ i)⌋₊ : ℝ) * (1 / 2 : ℝ) ^ (φ i)
    linarith
  · exact floor_mul_le ht (by positivity)

lemma gpath_nonpos (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) {t : ℝ} (ht : t ≤ 0) :
    gpath hf hx0 k t = x0 := by
  unfold gpath
  rw [Nat.floor_of_nonpos (div_nonpos_iff.2 (Or.inr ⟨ht, by positivity⟩))]
  rfl

lemma gpath_fin (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) (t : ℝ) :
    f (gpath hf hx0 k t) ≠ ⊤ :=
  (schemeX_isScheme hf hx0 k).fin _

lemma gpath_le (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) (t : ℝ) :
    f (gpath hf hx0 k t) ≤ f x0 := by
  have hX := schemeX_isScheme hf hx0 k
  show f (schemeX hf hx0 k ⌊t / (1 / 2 : ℝ) ^ k⌋₊) ≤ f (schemeX hf hx0 k 0)
  rw [hX.coe ⌊t / (1 / 2 : ℝ) ^ k⌋₊, hX.coe 0]
  exact EReal.coe_le_coe_iff.2 (hX.F_anti (Nat.zero_le _))

lemma gpath_dist (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖gpath hf hx0 k t - x0‖ ≤ Real.sqrt (2 * t * ((f x0).toReal - m)) := by
  have hX := schemeX_isScheme hf hx0 k
  have h1 := hX.dist_sq hf.lb ⌊t / (1 / 2 : ℝ) ^ k⌋₊
  rw [Fv_zero] at h1
  have hf0m : m ≤ (f x0).toReal := by
    have := hX.F_ge hf.lb 0
    rwa [Fv_zero] at this
  have h2 := floor_mul_le ht (by positivity : (0 : ℝ) < (1 / 2) ^ k)
  apply Real.le_sqrt_of_sq_le
  show ‖schemeX hf hx0 k ⌊t / (1 / 2 : ℝ) ^ k⌋₊ - schemeX hf hx0 k 0‖ ^ 2 ≤ _
  refine h1.trans ?_
  have := sub_nonneg.2 hf0m
  nlinarith

/-- Uniform (in `k ≥ k0`) Lipschitz and discrete-LEVI bounds for the interpolants on `[0,T]`. -/
theorem gpath_bounds (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) {w : E} (hw : w ∈ LimitingSubdiff f x0)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ L ρ δ : ℝ, ∃ k0 : ℕ, 0 ≤ ρ ∧ 0 < δ ∧ 0 ≤ L ∧ ∀ k ≥ k0,
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        ‖gpath hf hx0 k t - gpath hf hx0 k s‖ ≤ L * (t - s + (1 / 2) ^ k)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ y : E, ∀ b : ℝ, f y ≤ b →
        ‖y - gpath hf hx0 k t‖ + L * (t - s + (1 / 2) ^ k) ≤ δ →
        ‖y - gpath hf hx0 k t‖ ^ 2 / 2 - ‖y - gpath hf hx0 k s‖ ^ 2 / 2 ≤
          (gridT k t - gridT k s) * (b - (f (gpath hf hx0 k t)).toReal) +
          ρ * ((gridT k t - gridT k s) *
            (‖y - gpath hf hx0 k t‖ + L * (t - s + (1 / 2) ^ k)) ^ 2)) := by
  obtain ⟨R, ρ, δ, L, k0, hρ, hδ, hL, hS, -, hk⟩ := consts hf hx0 hw T hT
  refine ⟨L, ρ, δ, k0, hρ, hδ, hL, fun k hk' => ?_⟩
  obtain ⟨-, hball, -, hsp⟩ := hk k hk'
  have hX := schemeX_isScheme hf hx0 k
  set h := (1 / 2 : ℝ) ^ k with hh
  have hhpos : 0 < h := by positivity
  have glip : ∀ i d : ℕ, ((i : ℝ) + d) * h ≤ T + 1 →
      ‖schemeX hf hx0 k (i + d) - schemeX hf hx0 k i‖ ≤ d * (h * L) := by
    intro i d hid
    refine grid_lip d (fun i' h1 h2 => hsp i' ?_)
    have : (i' : ℝ) + 1 ≤ (i : ℝ) + d := by exact_mod_cast (show i' + 1 ≤ i + d by omega)
    nlinarith
  refine ⟨fun s t hs hst htT => ?_, fun s t hs hst htT y b hb hyδ => ?_⟩
  · set a := ⌊s / h⌋₊ with ha
    set c := ⌊t / h⌋₊ with hc
    have hac : a ≤ c := Nat.floor_mono (div_le_div_of_nonneg_right hst hhpos.le)
    have hct : (c : ℝ) * h ≤ t := floor_mul_le (hs.trans hst) hhpos
    have has : s < ((a : ℝ) + 1) * h := lt_floor_mul hhpos
    have e : ((a : ℝ) + ((c - a : ℕ) : ℝ)) = c := by rw [Nat.cast_sub hac]; ring
    have hg := glip a (c - a) (by rw [e]; linarith)
    rw [show a + (c - a) = c by omega, Nat.cast_sub hac] at hg
    show ‖schemeX hf hx0 k c - schemeX hf hx0 k a‖ ≤ L * (t - s + h)
    refine hg.trans ?_
    have : ((c : ℝ) - a) * h ≤ t - s + h := by linarith
    nlinarith
  · set a := ⌊s / h⌋₊ with ha
    set c := ⌊t / h⌋₊ with hc
    have hac : a ≤ c := Nat.floor_mono (div_le_div_of_nonneg_right hst hhpos.le)
    have hct : (c : ℝ) * h ≤ t := floor_mul_le (hs.trans hst) hhpos
    have has : s < ((a : ℝ) + 1) * h := lt_floor_mul hhpos
    have hK : ∀ i, a < i → i ≤ c → schemeX hf hx0 k i ∈ Metric.closedBall (0 : E) R := by
      intro i _ hi
      rw [mem_closedBall_zero_iff]
      have : (i : ℝ) * h ≤ T + 1 := by
        have : (i : ℝ) ≤ c := by exact_mod_cast hi
        nlinarith
      linarith [hball i this]
    have hr : ∀ i, a < i → i ≤ c →
        ‖y - schemeX hf hx0 k i‖ ≤ ‖y - schemeX hf hx0 k c‖ + L * (t - s + h) := by
      intro i hi1 hi2
      have e : ((i : ℝ) + ((c - i : ℕ) : ℝ)) = c := by rw [Nat.cast_sub hi2]; ring
      have hg := glip i (c - i) (by rw [e]; linarith)
      rw [show i + (c - i) = c by omega] at hg
      have e2 : ((c - i : ℕ) : ℝ) ≤ (c : ℝ) - a - 1 := by
        rw [Nat.cast_sub hi2]
        have : (a : ℝ) + 1 ≤ i := by exact_mod_cast hi1
        linarith
      have e3 : ((c - i : ℕ) : ℝ) * h ≤ t - s + h := by
        have := mul_le_mul_of_nonneg_right e2 hhpos.le
        linarith
      have e4 : ((c - i : ℕ) : ℝ) * (h * L) ≤ L * (t - s + h) := by
        have := mul_le_mul_of_nonneg_right e3 hL
        linarith
      have := norm_sub_le_norm_sub_add_norm_sub y (schemeX hf hx0 k c) (schemeX hf hx0 k i)
      linarith
    have H := hX.levi hS hρ hac hb hK hr hyδ
    rw [Nat.cast_sub hac, sub_mul] at H
    show ‖y - schemeX hf hx0 k c‖ ^ 2 / 2 - ‖y - schemeX hf hx0 k a‖ ^ 2 / 2 ≤
      ((c : ℝ) * h - (a : ℝ) * h) * (b - Fv f (schemeX hf hx0 k) c) +
      ρ * (((c : ℝ) * h - (a : ℝ) * h) * (‖y - schemeX hf hx0 k c‖ + L * (t - s + h)) ^ 2)
    exact H

/-- **Existence of the limit curve** with a local Lipschitz bound and the local EVI. -/
theorem exists_limit_curve (hf : GoodF f m) (hx0 : f x0 ≠ ⊤) {w : E}
    (hw : w ∈ LimitingSubdiff f x0) :
    ∃ z : ℝ → E, z 0 = x0 ∧ (∀ t, f (z t) ≤ f x0) ∧
      ∀ T : ℝ, 0 ≤ T → ∃ L ρ δ : ℝ, 0 ≤ ρ ∧ 0 < δ ∧ 0 ≤ L ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ‖z t - z s‖ ≤ L * (t - s)) ∧
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ y : E, ∀ b : ℝ, f y ≤ b →
          ‖y - z t‖ + L * (t - s) < δ →
          ‖y - z t‖ ^ 2 / 2 - ‖y - z s‖ ^ 2 / 2 ≤
            (t - s) * (b - (f (z t)).toReal) + ρ * ((t - s) * (‖y - z t‖ + L * (t - s)) ^ 2)) := by
  obtain ⟨φ, hφ, hdy⟩ := diag_subseq
    (fun k (p : ℕ × ℕ) => gpath hf hx0 k ((p.2 : ℝ) / 2 ^ p.1)) x0
    (fun p => Real.sqrt (2 * ((p.2 : ℝ) / 2 ^ p.1) * ((f x0).toReal - m)))
    (fun k p => gpath_dist hf hx0 k (by positivity))
  have hconv := conv_all (gpath hf hx0) φ hφ (fun l j => hdy (l, j)) (gpath_mod hf hx0 hw)
  have hall : ∀ t : ℝ, ∃ A : E, Tendsto (fun i => gpath hf hx0 (φ i) t) atTop (𝓝 A) := by
    intro t
    rcases le_total 0 t with ht | ht
    · exact hconv t ht
    · refine ⟨x0, ?_⟩
      simp only [gpath_nonpos hf hx0 _ ht]
      exact tendsto_const_nhds
  choose z hz using hall
  have hz0 : z 0 = x0 := by
    refine tendsto_nhds_unique (hz 0) ?_
    simp only [gpath_nonpos hf hx0 _ le_rfl]
    exact tendsto_const_nhds
  have hzle : ∀ t, f (z t) ≤ f x0 := by
    intro t
    by_contra hlt
    obtain ⟨i, hi⟩ := ((hz t).eventually (hf.lsc (z t) (f x0) (not_le.1 hlt))).exists
    exact absurd (gpath_le hf hx0 (φ i) t) (not_le.2 hi)
  refine ⟨z, hz0, hzle, fun T hT => ?_⟩
  obtain ⟨L, ρ, δ, k0, hρ, hδ, hL, hk⟩ := gpath_bounds hf hx0 hw T hT
  have hev : ∀ᶠ i in atTop, k0 ≤ φ i := hφ.tendsto_atTop.eventually_ge_atTop k0
  have hh := tendsto_half_pow hφ
  have hLs : ∀ s t : ℝ, Tendsto (fun i => L * (t - s + (1 / 2 : ℝ) ^ (φ i))) atTop
      (𝓝 (L * (t - s))) := by
    intro s t
    simpa using ((tendsto_const_nhds (x := t - s)).add hh).const_mul L
  refine ⟨L, ρ, δ, hρ, hδ, hL, fun s t hs hst htT => ?_, fun s t hs hst htT y b hb hyδ => ?_⟩
  · refine le_of_tendsto_of_tendsto ((hz t).sub (hz s)).norm (hLs s t) ?_
    filter_upwards [hev] with i hi
    exact (hk (φ i) hi).1 s t hs hst htT
  · set Fz := (f (z t)).toReal with hFz
    have hFz_top : f (z t) ≠ ⊤ := ne_top_of_le_ne_top hx0 (hzle t)
    have hD : Tendsto (fun i => gridT (φ i) t - gridT (φ i) s) atTop (𝓝 (t - s)) :=
      (tendsto_gridT hφ (hs.trans hst)).sub (tendsto_gridT hφ hs)
    have hr : Tendsto (fun i => ‖y - gpath hf hx0 (φ i) t‖ + L * (t - s + (1 / 2 : ℝ) ^ (φ i)))
        atTop (𝓝 (‖y - z t‖ + L * (t - s))) :=
      ((tendsto_const_nhds.sub (hz t)).norm).add (hLs s t)
    have hLHS : Tendsto (fun i => ‖y - gpath hf hx0 (φ i) t‖ ^ 2 / 2 -
        ‖y - gpath hf hx0 (φ i) s‖ ^ 2 / 2) atTop
        (𝓝 (‖y - z t‖ ^ 2 / 2 - ‖y - z s‖ ^ 2 / 2)) :=
      ((((tendsto_const_nhds.sub (hz t)).norm).pow 2).div_const 2).sub
        ((((tendsto_const_nhds.sub (hz s)).norm).pow 2).div_const 2)
    have hε : ∀ ε : ℝ, 0 < ε → ‖y - z t‖ ^ 2 / 2 - ‖y - z s‖ ^ 2 / 2 ≤
        (t - s) * (b - Fz + ε) + ρ * ((t - s) * (‖y - z t‖ + L * (t - s)) ^ 2) := by
      intro ε hε
      have hlt : ((Fz - ε : ℝ) : EReal) < f (z t) := by
        calc ((Fz - ε : ℝ) : EReal) < ((Fz : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
          _ = f (z t) := EReal.coe_toReal hFz_top (hf.bot _)
      have e3 := (hz t).eventually (hf.lsc (z t) _ hlt)
      have e2 := hr.eventually (gt_mem_nhds hyδ)
      refine le_of_tendsto_of_tendsto hLHS
        ((hD.mul_const (b - Fz + ε)).add ((hD.mul (hr.pow 2)).const_mul ρ)) ?_
      filter_upwards [hev, e2, e3] with i hi h2 h3
      have H1 := (hk (φ i) hi).2 s t hs hst htT y b hb h2.le
      have hc := EReal.coe_toReal (gpath_fin hf hx0 (φ i) t) (hf.bot _)
      rw [← hc] at h3
      have h3' := EReal.coe_lt_coe_iff.1 h3
      have hD0 : 0 ≤ gridT (φ i) t - gridT (φ i) s := sub_nonneg.2 (gridT_mono _ hst)
      have := mul_le_mul_of_nonneg_left
        (show b - (f (gpath hf hx0 (φ i) t)).toReal ≤ b - Fz + ε by linarith) hD0
      linarith
    refine le_of_forall_pos_le_add fun ε hεpos => ?_
    have hts : 0 ≤ t - s := sub_nonneg.2 hst
    have H := hε (ε / (t - s + 1)) (by positivity)
    have e1 : (t - s) * (ε / (t - s + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      nlinarith
    have e2 : (t - s) * (b - Fz + ε / (t - s + 1)) =
        (t - s) * (b - Fz) + (t - s) * (ε / (t - s + 1)) := by ring
    linarith

end Limit

/-! ## L6a: trajectory properties of a curve satisfying the local EVI -/

section TrajProps

/-- Lipschitz bound and local EVI of a curve on `[0,T]` (the output of `exists_limit_curve`). -/
def LeviData (f : E → EReal) (z : ℝ → E) (T L ρ δ : ℝ) : Prop :=
  0 ≤ ρ ∧ 0 < δ ∧ 0 ≤ L ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ‖z t - z s‖ ≤ L * (t - s)) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ y : E, ∀ b : ℝ, f y ≤ b →
      ‖y - z t‖ + L * (t - s) < δ →
      ‖y - z t‖ ^ 2 / 2 - ‖y - z s‖ ^ 2 / 2 ≤
        (t - s) * (b - (f (z t)).toReal) + ρ * ((t - s) * (‖y - z t‖ + L * (t - s)) ^ 2))

variable [FiniteDimensional ℝ E] {f : E → EReal} {z : ℝ → E} {T L ρ δ : ℝ}

lemma LeviData.lipschitzOnWith (hD : LeviData f z T L ρ δ) :
    LipschitzOnWith (Real.toNNReal L) z (Set.Icc 0 T) := by
  obtain ⟨-, -, hL, hlip, -⟩ := hD
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Real.coe_toNNReal _ hL, dist_eq_norm, Real.dist_eq]
  rcases le_total a b with hab | hab
  · rw [← norm_neg, neg_sub, abs_of_nonpos (sub_nonpos.2 hab)]
    have := hlip a b ha.1 hab hb.2
    linarith
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]
    exact hlip b a hb.1 hab ha.2

lemma LeviData.ac (hD : LeviData f z T L ρ δ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval z 0 T := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal L)
  rw [Set.uIcc_of_le hT]
  exact hD.lipschitzOnWith

lemma slope_smul_eq {g : ℝ → E} {s t : ℝ} (h : s ≠ t) :
    g t - g s = (t - s) • slope g t s := by
  rw [slope_def_module, smul_smul, ← neg_sub s t, neg_mul, mul_inv_cancel₀ (sub_ne_zero.2 h),
    neg_one_smul, neg_sub]

lemma exists_left_seq {t : ℝ} (ht : 0 < t) :
    ∃ s : ℕ → ℝ, (∀ n, 0 ≤ s n) ∧ (∀ n, s n < t) ∧ Tendsto s atTop (𝓝 t) := by
  refine ⟨fun n => t - t * (1 / ((n : ℝ) + 1)), fun n => ?_, fun n => ?_, ?_⟩
  · have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have h2 : t * (1 / ((n : ℝ) + 1)) ≤ t * 1 := mul_le_mul_of_nonneg_left h1 ht.le
    show 0 ≤ t - t * (1 / ((n : ℝ) + 1))
    linarith
  · have : 0 < t * (1 / ((n : ℝ) + 1)) := by positivity
    show t - t * (1 / ((n : ℝ) + 1)) < t
    linarith
  · simpa using (tendsto_const_nhds (x := t)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t)

/-- Limits of backward difference quotients are (negated) local subgradients. -/
lemma LeviData.locSubgrad (hD : LeviData f z T L ρ δ) (hbot : ∀ y, f y ≠ ⊥) {t : ℝ}
    (htT : t ≤ T) (hfin : f (z t) ≠ ⊤) {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t)
    (hs : Tendsto s atTop (𝓝 t)) {q : E}
    (hq : Tendsto (fun n => slope z t (s n)) atTop (𝓝 q)) :
    LocSubgrad f (z t) (-q) ρ δ := by
  obtain ⟨hρ, hδ, hL, hlip, hlevi⟩ := hD
  refine ⟨hfin, fun y hy => ?_⟩
  by_cases hyt : f y = ⊤
  · rw [hyt]; exact le_top
  set b := (f y).toReal with hb
  have hfy : f y = (b : EReal) := (EReal.coe_toReal hyt (hbot y)).symm
  set Fz := (f (z t)).toReal with hFz
  have hfz : f (z t) = (Fz : EReal) := (EReal.coe_toReal hfin (hbot _)).symm
  set a := y - z t with ha
  suffices H : Fz + (⟪-q, a⟫_ℝ - ρ * ‖a‖ ^ 2) ≤ b by
    rw [hfz, hfy, ← EReal.coe_add]; exact EReal.coe_le_coe_iff.2 H
  have hτ : Tendsto (fun n => t - s n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := t)).sub hs
  have h2 : Tendsto (fun n => ‖a‖ + L * (t - s n)) atTop (𝓝 ‖a‖) := by
    simpa using (tendsto_const_nhds (x := ‖a‖)).add (hτ.const_mul L)
  have hu : Tendsto (fun n => -⟪a, slope z t (s n)⟫_ℝ - ρ * (‖a‖ + L * (t - s n)) ^ 2 -
      L ^ 2 * (t - s n) / 2) atTop (𝓝 (-⟪a, q⟫_ℝ - ρ * ‖a‖ ^ 2)) := by
    have h1 : Tendsto (fun n => ⟪a, slope z t (s n)⟫_ℝ) atTop (𝓝 ⟪a, q⟫_ℝ) :=
      tendsto_const_nhds.inner hq
    have h3 : Tendsto (fun n => L ^ 2 * (t - s n) / 2) atTop (𝓝 0) := by
      simpa using (hτ.const_mul (L ^ 2)).div_const 2
    simpa using (h1.neg.sub ((h2.pow 2).const_mul ρ)).sub h3
  have hev : ∀ᶠ n in atTop, ‖a‖ + L * (t - s n) < δ := h2.eventually (gt_mem_nhds hy)
  have hlim := le_of_tendsto hu (hev.mono fun n hn => by
    have H := hlevi (s n) t (hs0 n) (hst n).le htT y b hfy.le hn
    have hy' : y - z (s n) = a + (z t - z (s n)) := by rw [ha]; abel
    have hexp : ‖y - z (s n)‖ ^ 2 =
        ‖a‖ ^ 2 + 2 * ⟪a, z t - z (s n)⟫_ℝ + ‖z t - z (s n)‖ ^ 2 := by
      rw [hy', norm_add_sq_real]
    have hinner : ⟪a, z t - z (s n)⟫_ℝ = (t - s n) * ⟪a, slope z t (s n)⟫_ℝ := by
      rw [slope_smul_eq (hst n).ne, real_inner_smul_right]
    have hdn := hlip (s n) t (hs0 n) (hst n).le htT
    have hdsq : ‖z t - z (s n)‖ ^ 2 ≤ (L * (t - s n)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hdn 2
    have key : (t - s n) * (-⟪a, slope z t (s n)⟫_ℝ - ρ * (‖a‖ + L * (t - s n)) ^ 2 -
        L ^ 2 * (t - s n) / 2) ≤ (t - s n) * (b - Fz) := by
      nlinarith
    exact le_of_mul_le_mul_left key (sub_pos.2 (hst n)))
  rw [inner_neg_left, real_inner_comm a q]
  linarith

lemma LeviData.subdiff_nonempty (hD : LeviData f z T L ρ δ) (hbot : ∀ y, f y ≠ ⊥) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (hfin : f (z t) ≠ ⊤) : (LimitingSubdiff f (z t)).Nonempty := by
  obtain ⟨s, hs0, hst, hs⟩ := exists_left_seq ht
  have hbd : ∀ n, slope z t (s n) ∈ Metric.closedBall (0 : E) L := by
    intro n
    rw [mem_closedBall_zero_iff]
    have h1 := hD.2.2.2.1 (s n) t (hs0 n) (hst n).le htT
    rw [slope_smul_eq (hst n).ne, norm_smul, Real.norm_eq_abs,
      abs_of_pos (sub_pos.2 (hst n))] at h1
    exact le_of_mul_le_mul_left (h1.trans_eq (mul_comm _ _)) (sub_pos.2 (hst n))
  obtain ⟨q, -, ψ, hψ, hq⟩ := (isCompact_closedBall (0 : E) L).tendsto_subseq hbd
  have hloc := hD.locSubgrad hbot htT hfin (s := s ∘ ψ) (fun n => hs0 _) (fun n => hst _)
    (hs.comp hψ.tendsto_atTop) hq
  exact ⟨-q, IsRegularSubgrad.mem_limitingSubdiff (hloc.isRegularSubgrad hD.1 hD.2.1)⟩

lemma LeviData.deriv_subgrad (hD : LeviData f z T L ρ δ) (hbot : ∀ y, f y ≠ ⊥) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (hfin : f (z t) ≠ ⊤) {v : E} (hv : HasDerivAt z v t) :
    -v ∈ LimitingSubdiff f (z t) := by
  obtain ⟨s, hs0, hst, hs⟩ := exists_left_seq ht
  have hq : Tendsto (fun n => slope z t (s n)) atTop (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope.1 hv).comp (tendsto_nhdsWithin_iff.2
      ⟨hs, Eventually.of_forall fun n => Set.mem_compl_singleton_iff.2 (hst n).ne⟩)
  have hloc := hD.locSubgrad hbot htT hfin hs0 hst hs hq
  exact IsRegularSubgrad.mem_limitingSubdiff (hloc.isRegularSubgrad hD.1 hD.2.1)

lemma ae_hasDeriv_subgrad (hbot : ∀ y, f y ≠ ⊥) (hfin : ∀ t, f (z t) ≠ ⊤)
    (hz : ∀ T : ℝ, 0 ≤ T → ∃ L ρ δ : ℝ, LeviData f z T L ρ δ) :
    ∀ᵐ t : ℝ, 0 < t → ∃ v, HasDerivAt z v t ∧ -v ∈ LimitingSubdiff f (z t) := by
  have hN : ∀ N : ℕ, ∀ᵐ t : ℝ, 0 < t → t < N →
      ∃ v, HasDerivAt z v t ∧ -v ∈ LimitingSubdiff f (z t) := by
    intro N
    obtain ⟨L, ρ, δ, hD⟩ := hz N (Nat.cast_nonneg N)
    have hpI : ∀ u : ℝ, max (min u N) 0 ∈ Set.Icc (0 : ℝ) N :=
      fun u => ⟨le_max_right _ _, max_le (min_le_right _ _) (Nat.cast_nonneg N)⟩
    have hlip : LipschitzWith (Real.toNNReal L) (fun u => z (max (min u N) 0)) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have h1 := hD.lipschitzOnWith.dist_le_mul _ (hpI a) _ (hpI b)
      have h2 : dist (max (min a N) 0) (max (min b N) 0) ≤ dist a b := by
        rw [Real.dist_eq, Real.dist_eq]
        refine (abs_max_sub_max_le_abs _ _ _).trans ?_
        refine (abs_min_sub_min_le_max a N b N).trans ?_
        simp
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg _))
    filter_upwards [hlip.ae_differentiableAt_real] with t hdiff ht htN
    have heq : z =ᶠ[𝓝 t] fun u => z (max (min u N) 0) := by
      filter_upwards [Ioo_mem_nhds ht htN] with u hu
      rw [min_eq_left hu.2.le, max_eq_left hu.1.le]
    have hv := hdiff.hasDerivAt.congr_of_eventuallyEq heq
    exact ⟨_, hv, hD.deriv_subgrad hbot ht htN.le (hfin t) hv⟩
  filter_upwards [MeasureTheory.ae_all_iff.2 hN] with t h ht
  obtain ⟨N, hN'⟩ := exists_nat_gt t
  exact h N ht hN'

end TrajProps

/-! ## L6b: energy dissipation and square-integrable velocity -/

section Energy

/-- A function with `g s - C (t-s)² ≤ g t` for nearby `s ≤ t` is monotone. -/
lemma mono_of_local {g : ℝ → ℝ} {a b C η : ℝ} (hη : 0 < η)
    (h : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → t - s < η → g s - C * (t - s) ^ 2 ≤ g t) :
    MonotoneOn g (Set.Icc a b) := by
  intro s hs t ht hst
  have key : ∀ n : ℕ, 0 < n → (t - s) / n < η → g s - C * (t - s) ^ 2 / n ≤ g t := by
    intro n hn hd
    set d := (t - s) / n with hddef
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hd0 : 0 ≤ d := div_nonneg (sub_nonneg.2 hst) hnpos.le
    have hnd : (n : ℝ) * d = t - s := by rw [hddef]; field_simp
    have hstep : ∀ i : ℕ, i ≤ n → g s - i * (C * d ^ 2) ≤ g (s + i * d) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have hi' : ((i : ℝ) + 1) ≤ n := by exact_mod_cast hi
        have hpt : s + ((i : ℝ) + 1) * d ≤ t := by nlinarith
        have h2 := h (s + i * d) (s + ((i : ℝ) + 1) * d) (by nlinarith [hs.1])
          (by nlinarith) (hpt.trans ht.2) (by nlinarith)
        have e : s + ((i : ℝ) + 1) * d - (s + i * d) = d := by ring
        rw [e] at h2
        push_cast
        linarith
    have := hstep n le_rfl
    have hst' : s + (n : ℝ) * d = t := by rw [hnd]; ring
    rw [hst'] at this
    have e2 : (n : ℝ) * (C * d ^ 2) = C * (t - s) ^ 2 / n := by
      rw [← hnd]; field_simp
    linarith
  have hlim : Tendsto (fun n : ℕ => g s - C * (t - s) ^ 2 / n) atTop (𝓝 (g s)) := by
    simpa using (tendsto_const_nhds (x := g s)).sub
      (tendsto_const_div_atTop_nhds_zero_nat (C * (t - s) ^ 2))
  have hlim2 : Tendsto (fun n : ℕ => (t - s) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (t - s)
  refine le_of_tendsto hlim ?_
  filter_upwards [hlim2.eventually (gt_mem_nhds hη), eventually_gt_atTop 0] with n h1 h2
  exact key n h2 h1

variable [FiniteDimensional ℝ E] {f : E → EReal} {z : ℝ → E} {T L ρ δ : ℝ}

lemma LeviData.energy (hD : LeviData f z T L ρ δ) (hbot : ∀ y, f y ≠ ⊥)
    (hfin : ∀ t, f (z t) ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (hδ : 2 * L * (t - s) < δ) :
    ‖z t - z s‖ ^ 2 / 2 ≤
      (t - s) * ((f (z s)).toReal - (f (z t)).toReal) + 4 * ρ * L ^ 2 * (t - s) ^ 3 := by
  obtain ⟨hρ, -, hL, hlip, hlevi⟩ := hD
  have hd := hlip s t hs hst htT
  have hd' : ‖z s - z t‖ ≤ L * (t - s) := by rw [norm_sub_rev]; exact hd
  have hb : f (z s) ≤ (((f (z s)).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (hfin s) (hbot _)).ge
  have H := hlevi s t hs hst htT (z s) _ hb (by linarith)
  rw [sub_self, norm_zero, norm_sub_rev] at H
  have hτ : 0 ≤ t - s := sub_nonneg.2 hst
  have h1 : (‖z t - z s‖ + L * (t - s)) ^ 2 ≤ (2 * L * (t - s)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : ρ * ((t - s) * (‖z t - z s‖ + L * (t - s)) ^ 2) ≤
      ρ * ((t - s) * (2 * L * (t - s)) ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hτ) hρ
  nlinarith

lemma LeviData.neg_phi_mono (hD : LeviData f z T L ρ δ) (hbot : ∀ y, f y ≠ ⊥)
    (hfin : ∀ t, f (z t) ≠ ⊤) :
    MonotoneOn (fun t => -(f (z t)).toReal) (Set.Icc 0 T) := by
  have hL := hD.2.2.1
  apply mono_of_local (η := δ / (2 * L + 1)) (C := 4 * ρ * L ^ 2) (by have := hD.2.1; positivity)
  intro s t hs hst htT hη
  have hτ : 0 ≤ t - s := sub_nonneg.2 hst
  have hδ' : 2 * L * (t - s) < δ := by
    rw [lt_div_iff₀ (by positivity)] at hη
    nlinarith
  have hE := hD.energy hbot hfin hs hst htT hδ'
  show -(f (z s)).toReal - 4 * ρ * L ^ 2 * (t - s) ^ 2 ≤ -(f (z t)).toReal
  rcases hτ.lt_or_eq with hpos | heq
  · have h0 : 0 ≤ ‖z t - z s‖ ^ 2 / 2 := by positivity
    have h3 : (t - s) * ((f (z t)).toReal - (f (z s)).toReal - 4 * ρ * L ^ 2 * (t - s) ^ 2) ≤
        (t - s) * 0 := by nlinarith
    have := le_of_mul_le_mul_left h3 hpos
    linarith
  · have : t = s := by linarith
    subst this
    simp

lemma LeviData.speed_sq_le (hD : LeviData f z T L ρ δ) (hbot : ∀ y, f y ≠ ⊥)
    (hfin : ∀ t, f (z t) ≠ ⊤) {t : ℝ} (ht : 0 < t) (htT : t ≤ T) {v : E}
    (hv : HasDerivAt z v t) {d : ℝ} (hψ : HasDerivAt (fun u => -(f (z u)).toReal) d t) :
    ‖v‖ ^ 2 / 2 ≤ d := by
  obtain ⟨s, hs0, hst, hs⟩ := exists_left_seq ht
  have hne : ∀ᶠ n in atTop, s n ∈ ({t}ᶜ : Set ℝ) :=
    Eventually.of_forall fun n => Set.mem_compl_singleton_iff.2 (hst n).ne
  have hq : Tendsto (fun n => slope z t (s n)) atTop (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope.1 hv).comp (tendsto_nhdsWithin_iff.2 ⟨hs, hne⟩)
  have hσ : Tendsto (fun n => slope (fun u => -(f (z u)).toReal) t (s n)) atTop (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.1 hψ).comp (tendsto_nhdsWithin_iff.2 ⟨hs, hne⟩)
  have hτ : Tendsto (fun n => t - s n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := t)).sub hs
  have hev : ∀ᶠ n in atTop, 2 * L * (t - s n) < δ := by
    have : Tendsto (fun n => 2 * L * (t - s n)) atTop (𝓝 0) := by
      simpa using hτ.const_mul (2 * L)
    exact this.eventually (gt_mem_nhds hD.2.1)
  have hR : Tendsto (fun n => slope (fun u => -(f (z u)).toReal) t (s n) +
      4 * ρ * L ^ 2 * (t - s n)) atTop (𝓝 d) := by
    simpa using hσ.add (hτ.const_mul (4 * ρ * L ^ 2))
  refine le_of_tendsto_of_tendsto ((hq.norm.pow 2).div_const 2) hR ?_
  filter_upwards [hev] with n hn
  have hpos : 0 < t - s n := sub_pos.2 (hst n)
  have hE := hD.energy hbot hfin (hs0 n) (hst n).le htT hn
  rw [slope_smul_eq (hst n).ne, norm_smul, Real.norm_eq_abs, abs_of_pos hpos] at hE
  have hψe := slope_smul_eq (E := ℝ) (g := fun u => -(f (z u)).toReal) (hst n).ne
  simp only [smul_eq_mul] at hψe
  have e : (t - s n) ^ 2 * slope (fun u => -(f (z u)).toReal) t (s n) =
      (t - s n) * ((f (z (s n))).toReal - (f (z t)).toReal) := by
    rw [pow_two, mul_assoc, ← hψe]; ring
  have key : (t - s n) ^ 2 * (‖slope z t (s n)‖ ^ 2 / 2) ≤ (t - s n) ^ 2 *
      (slope (fun u => -(f (z u)).toReal) t (s n) + 4 * ρ * L ^ 2 * (t - s n)) := by
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- Square-integrable velocity: `∫⁻_{(0,∞)} ‖ż‖² ≤ 2 (f(z 0) - m)`. -/
theorem lintegral_speed_le (hbot : ∀ y, f y ≠ ⊥) (hfin : ∀ t, f (z t) ≠ ⊤) {m : ℝ}
    (hlb : ∀ y, (m : EReal) ≤ f y)
    (hz : ∀ T : ℝ, 0 ≤ T → ∃ L ρ δ : ℝ, LeviData f z T L ρ δ) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ‖deriv z t‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * ((f (z 0)).toReal - m)) := by
  have hφm : ∀ u, m ≤ (f (z u)).toReal := by
    intro u
    have := hlb (z u)
    rwa [← EReal.coe_toReal (hfin u) (hbot _), EReal.coe_le_coe_iff] at this
  set g : ℝ → ENNReal := fun t => ‖deriv z t‖ₑ ^ 2 with hg
  borelize E
  have hgm : Measurable g := ((measurable_deriv z).enorm).pow_const 2
  have hN : ∀ N : ℕ, ∫⁻ t in Set.Ioc (0 : ℝ) N, g t ≤
      ENNReal.ofReal (2 * ((f (z 0)).toReal - m)) := by
    intro N
    obtain ⟨L, ρ, δ, hD⟩ := hz ((N : ℝ) + 1) (by positivity)
    set ψ : ℝ → ℝ := fun u => -(f (z u)).toReal with hψdef
    have hmono : MonotoneOn ψ (Set.Icc 0 ((N : ℝ) + 1)) := hD.neg_phi_mono hbot hfin
    have hpI : ∀ u : ℝ, max (min u ((N : ℝ) + 1)) 0 ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
      fun u => ⟨le_max_right _ _, max_le (min_le_right _ _) (by positivity)⟩
    have hmc : Monotone (fun u => ψ (max (min u ((N : ℝ) + 1)) 0)) := fun a b hab =>
      hmono (hpI a) (hpI b) (max_le_max (min_le_min hab le_rfl) le_rfl)
    have hmonoN : MonotoneOn ψ (Set.uIcc 0 (N : ℝ)) := by
      rw [Set.uIcc_of_le (Nat.cast_nonneg N)]
      exact hmono.mono (Set.Icc_subset_Icc le_rfl (by linarith))
    have hpt : ∀ᵐ t : ℝ, t ∈ Set.Ioc (0 : ℝ) N →
        0 ≤ 2 * deriv ψ t ∧ g t ≤ ENNReal.ofReal (2 * deriv ψ t) := by
      filter_upwards [hmc.ae_differentiableAt, ae_hasDeriv_subgrad hbot hfin hz] with t h1 h2 ht
      obtain ⟨v, hv, -⟩ := h2 ht.1
      have heq : ψ =ᶠ[𝓝 t] fun u => ψ (max (min u ((N : ℝ) + 1)) 0) := by
        filter_upwards [Ioo_mem_nhds ht.1 (by linarith [ht.2] : t < (N : ℝ) + 1)] with u hu
        rw [min_eq_left hu.2.le, max_eq_left hu.1.le]
      have hψd := h1.hasDerivAt.congr_of_eventuallyEq heq
      have hsq := hD.speed_sq_le hbot hfin ht.1 (by linarith [ht.2]) hv hψd
      rw [hψd.deriv]
      refine ⟨by nlinarith [sq_nonneg ‖v‖], ?_⟩
      show ‖deriv z t‖ₑ ^ 2 ≤ _
      rw [hv.deriv, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hpt' := (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) measurableSet_Ioc).2 hpt
    have hint : MeasureTheory.IntegrableOn (fun t => 2 * deriv ψ t) (Set.Ioc (0 : ℝ) N) :=
      (hmonoN.intervalIntegrable_deriv).1.const_mul 2
    calc ∫⁻ t in Set.Ioc (0 : ℝ) N, g t
        ≤ ∫⁻ t in Set.Ioc (0 : ℝ) N, ENNReal.ofReal (2 * deriv ψ t) :=
          MeasureTheory.lintegral_mono_ae (hpt'.mono fun t ht => ht.2)
      _ = ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) N, 2 * deriv ψ t) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (hpt'.mono fun t ht => ht.1)).symm
      _ ≤ ENNReal.ofReal (2 * ((f (z 0)).toReal - m)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
          have hmem := hmonoN.intervalIntegral_deriv_mem_uIcc
          have h0 := hφm (N : ℝ)
          have h1 : ψ N - ψ 0 = (f (z 0)).toReal - (f (z N)).toReal := by
            simp only [hψdef]; ring
          have h2 := hφm 0
          rcases Set.mem_uIcc.1 hmem with h | h <;> nlinarith [h.1, h.2]
  have hind : ∀ t, (Set.Ioi (0 : ℝ)).indicator g t = ⨆ N : ℕ, (Set.Ioc (0 : ℝ) N).indicator g t := by
    intro t
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from ht)]
      obtain ⟨N, hN'⟩ := exists_nat_gt t
      refine le_antisymm (le_iSup_of_le N ?_) (iSup_le fun N => Set.indicator_le_self _ _ t)
      rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) N from ⟨ht, hN'.le⟩)]
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from ht)]
      symm
      refine le_antisymm (iSup_le fun N => ?_) (by simp)
      rw [Set.indicator_of_notMem (show t ∉ Set.Ioc (0 : ℝ) N from fun h => ht h.1)]
  have hgoal : ∫⁻ t in Set.Ioi (0 : ℝ), g t = ⨆ N : ℕ, ∫⁻ t in Set.Ioc (0 : ℝ) N, g t := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioi, MeasureTheory.lintegral_congr hind,
      MeasureTheory.lintegral_iSup (fun N => hgm.indicator measurableSet_Ioc)
        (fun N M hNM t => Set.indicator_le_indicator_of_subset
          (Set.Ioc_subset_Ioc le_rfl (by exact_mod_cast hNM)) (fun _ => by simp) t)]
    exact iSup_congr fun N => MeasureTheory.lintegral_indicator measurableSet_Ioc g
  show ∫⁻ t in Set.Ioi (0 : ℝ), g t ≤ _
  rw [hgoal]
  exact iSup_le hN

end Energy

/-! ## L7: uniqueness of trajectories (hypomonotonicity + local Gronwall) -/

section Unique

lemma ac_norm_sq {u : ℝ → E} {a b : ℝ} (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => ‖u t‖ ^ 2) a b := by
  obtain ⟨C, hC⟩ := hu.exists_bound
  set M := |C| + 1 with hM
  have hMpos : 0 < M := by positivity
  have hCM : ∀ x ∈ Set.uIcc a b, ‖u x‖ ≤ M := fun x hx =>
    (hC x hx).trans (by rw [hM]; linarith [le_abs_self C])
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hu (ε / (2 * M)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hpt : ∀ i ∈ Finset.range E.1, dist (‖u (E.2 i).1‖ ^ 2) (‖u (E.2 i).2‖ ^ 2) ≤
      2 * M * dist (u (E.2 i).1) (u (E.2 i).2) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hE.1 i hi
    have hp := hCM _ h1
    have hq := hCM _ h2
    rw [Real.dist_eq, dist_eq_norm]
    have e : ‖u (E.2 i).1‖ ^ 2 - ‖u (E.2 i).2‖ ^ 2 =
        (‖u (E.2 i).1‖ - ‖u (E.2 i).2‖) * (‖u (E.2 i).1‖ + ‖u (E.2 i).2‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u (E.2 i).1‖ + ‖u (E.2 i).2‖)]
    have h3 := abs_norm_sub_norm_le (u (E.2 i).1) (u (E.2 i).2)
    calc |‖u (E.2 i).1‖ - ‖u (E.2 i).2‖| * (‖u (E.2 i).1‖ + ‖u (E.2 i).2‖)
        ≤ ‖u (E.2 i).1 - u (E.2 i).2‖ * (2 * M) :=
          mul_le_mul h3 (by linarith) (by positivity) (norm_nonneg _)
      _ = 2 * M * ‖u (E.2 i).1 - u (E.2 i).2‖ := by ring
  calc ∑ i ∈ Finset.range E.1, dist (‖u (E.2 i).1‖ ^ 2) (‖u (E.2 i).2‖ ^ 2)
      ≤ ∑ i ∈ Finset.range E.1, 2 * M * dist (u (E.2 i).1) (u (E.2 i).2) :=
        Finset.sum_le_sum hpt
    _ = 2 * M * ∑ i ∈ Finset.range E.1, dist (u (E.2 i).1) (u (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ < 2 * M * (ε / (2 * M)) := mul_lt_mul_of_pos_left (H E hE hlen) (by positivity)
    _ = ε := by field_simp

/-- Limiting subgradients of a locally semiconvex function are locally hypomonotone. -/
lemma hypomono {f : E → EReal} {R ρ δ : ℝ} (hS : SemiconvOn f (Metric.closedBall 0 R) ρ δ)
    (hρ : 0 ≤ ρ) (hbot : ∀ z, f z ≠ ⊥) {a b v w : E} (ha : ‖a‖ < R) (hb : ‖b‖ < R)
    (hv : v ∈ LimitingSubdiff f a) (hw : w ∈ LimitingSubdiff f b) (hab : ‖a - b‖ < δ) :
    -(2 * ρ * ‖a - b‖ ^ 2) ≤ ⟪v - w, a - b⟫_ℝ := by
  have h1 := limiting_locSubgrad hS hρ hbot ha hv
  have h2 := limiting_locSubgrad hS hρ hbot hb hw
  have e1 := h1.2 b (by rwa [norm_sub_rev])
  have e2 := h2.2 a hab
  rw [← EReal.coe_toReal h1.1 (hbot a), ← EReal.coe_toReal h2.1 (hbot b), ← EReal.coe_add,
    EReal.coe_le_coe_iff] at e1 e2
  rw [norm_sub_rev b a] at e1
  have : ⟪v, b - a⟫_ℝ = -⟪v, a - b⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  rw [inner_sub_left]
  linarith

/-- **Uniqueness**: two trajectories on `[0,b]` with the same initial point coincide. -/
theorem traj_unique {f : E → EReal} {m : ℝ} (hf : GoodF f m) {x z : ℝ → E} {b : ℝ}
    (hxac : AbsolutelyContinuousOnInterval x 0 b) (hzac : AbsolutelyContinuousOnInterval z 0 b)
    (hxd : ∀ᵐ t : ℝ, 0 < t → t < b → ∃ v, HasDerivAt x v t ∧ -v ∈ LimitingSubdiff f (x t))
    (hzd : ∀ᵐ t : ℝ, 0 < t → t < b → ∃ v, HasDerivAt z v t ∧ -v ∈ LimitingSubdiff f (z t))
    (h0 : x 0 = z 0) : ∀ t ∈ Set.Icc 0 b, x t = z t := by
  rcases lt_or_ge b 0 with hb | hb
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.2 hb)
  have hI : Set.uIcc 0 b = Set.Icc 0 b := Set.uIcc_of_le hb
  have hxc : ContinuousOn x (Set.Icc 0 b) := hI ▸ hxac.continuousOn
  have hzc : ContinuousOn z (Set.Icc 0 b) := hI ▸ hzac.continuousOn
  obtain ⟨Cx, hCx⟩ := hxac.exists_bound
  obtain ⟨Cz, hCz⟩ := hzac.exists_bound
  set R := max Cx Cz + 1 with hR
  have hxR : ∀ t ∈ Set.Icc 0 b, ‖x t‖ < R := fun t ht => by
    have := hCx t (hI ▸ ht); have := le_max_left Cx Cz; linarith
  have hzR : ∀ t ∈ Set.Icc 0 b, ‖z t‖ < R := fun t ht => by
    have := hCz t (hI ▸ ht); have := le_max_right Cx Cz; linarith
  obtain ⟨ρ, δ, hρ, hδ, hS⟩ := hf.semi R
  set g : ℝ → ℝ := fun t => ‖x t - z t‖ ^ 2 with hg
  have huac : AbsolutelyContinuousOnInterval (fun t => x t - z t) 0 b := hxac.sub hzac
  have hgac : AbsolutelyContinuousOnInterval g 0 b := ac_norm_sq huac
  have huc : ContinuousOn (fun t => x t - z t) (Set.Icc 0 b) := hxc.sub hzc
  have hgc : ContinuousOn g (Set.Icc 0 b) := huc.norm.pow 2
  have hder : ∀ᵐ s : ℝ, 0 < s → s < b → ‖x s - z s‖ < δ → deriv g s ≤ 4 * ρ * g s := by
    filter_upwards [hxd, hzd] with s h1 h2 hs hsb hsδ
    obtain ⟨vx, hvx, hx'⟩ := h1 hs hsb
    obtain ⟨vz, hvz, hz'⟩ := h2 hs hsb
    have hgd : HasDerivAt g (2 * ⟪x s - z s, vx - vz⟫_ℝ) s := (hvx.sub hvz).norm_sq
    have hsI : s ∈ Set.Icc 0 b := ⟨hs.le, hsb.le⟩
    have hh := hypomono hS hρ hf.bot (hxR s hsI) (hzR s hsI) hx' hz' hsδ
    have e : ⟪-vx - -vz, x s - z s⟫_ℝ = -⟪x s - z s, vx - vz⟫_ℝ := by
      rw [show -vx - -vz = -(vx - vz) by abel, inner_neg_left, real_inner_comm]
    rw [hgd.deriv]
    show 2 * ⟪x s - z s, vx - vz⟫_ℝ ≤ 4 * ρ * ‖x s - z s‖ ^ 2
    linarith
  have hS0 : IsClosed ({t | x t - z t = 0} ∩ Set.Icc 0 b) := by
    rw [Set.inter_comm]
    exact huc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have key := IsClosed.Icc_subset_of_forall_mem_nhdsWithin hS0
    (show x 0 - z 0 = 0 from sub_eq_zero.2 h0) ?_
  · intro t ht; exact sub_eq_zero.1 (key ht)
  rintro t1 ⟨ht1 : x t1 - z t1 = 0, ht1I⟩
  have hcw := huc t1 (Set.Ico_subset_Icc_self ht1I)
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨η, hη, hηu⟩ := hcw δ hδ
  set ε := min (η / 2) (min ((b - t1) / 2) (1 / (8 * ρ + 1))) with hεdef
  have hbt : 0 < b - t1 := sub_pos.2 ht1I.2
  have hεpos : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεη : ε < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεb : t1 + ε < b := by
    have h' : ε ≤ (b - t1) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hερ : 4 * ρ * ε < 1 := by
    have h' : ε ≤ 1 / (8 * ρ + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h'' : ε * (8 * ρ + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at h'
    nlinarith
  have hsub : Set.Icc t1 (t1 + ε) ⊆ Set.Icc 0 b := fun s hs => ⟨ht1I.1.trans hs.1, by linarith [hs.2]⟩
  have hsmall : ∀ s ∈ Set.Icc t1 (t1 + ε), ‖x s - z s‖ < δ := by
    intro s hs
    have hd : dist s t1 < η := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]; linarith [hs.2]
    have := hηu (hsub hs) hd
    rwa [dist_eq_norm, ht1, sub_zero] at this
  obtain ⟨t2, ht2, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (by linarith : t1 ≤ t1 + ε)) (hgc.mono hsub)
  have hmax' : ∀ s ∈ Set.Icc t1 (t1 + ε), g s ≤ g t2 := fun s hs => isMaxOn_iff.1 hmax s hs
  have hsub2 : Set.uIcc t1 t2 ⊆ Set.uIcc 0 b := by
    rw [Set.uIcc_of_le ht2.1, hI]
    exact fun s hs => hsub ⟨hs.1, hs.2.trans ht2.2⟩
  have hgac2 := hgac.mono hsub2
  have hFTC := hgac2.integral_deriv_eq_sub
  have hg1 : g t1 = 0 := by show ‖x t1 - z t1‖ ^ 2 = 0; rw [ht1, norm_zero]; ring
  have hne : ∀ᵐ s : ℝ, s ≠ t1 := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  have hae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc t1 t2)),
      deriv g s ≤ 4 * ρ * g t2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hder, hne] with s h hs' hs
    have hs1 : t1 < s := lt_of_le_of_ne hs.1 (Ne.symm hs')
    have hsI : s ∈ Set.Icc t1 (t1 + ε) := ⟨hs.1, hs.2.trans ht2.2⟩
    have := h (by linarith [ht1I.1]) (by linarith [hs.2, ht2.2]) (hsmall s hsI)
    have := hmax' s hsI
    nlinarith
  have hbound := intervalIntegral.integral_mono_ae_restrict ht2.1
    hgac2.intervalIntegrable_deriv intervalIntegrable_const hae
  rw [hFTC, hg1, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hbound
  have hg2 : 0 ≤ g t2 := by positivity
  have hg2' : g t2 ≤ 0 := by
    have h' : (t2 - t1) * (4 * ρ * g t2) ≤ ε * (4 * ρ * g t2) :=
      mul_le_mul_of_nonneg_right (by linarith [ht2.2]) (by positivity)
    nlinarith
  have hzero : ∀ s ∈ Set.Icc t1 (t1 + ε), x s - z s = 0 := by
    intro s hs
    have h1 := (hmax' s hs).trans hg2'
    have h2 : ‖x s - z s‖ ^ 2 ≤ 0 := h1
    have : ‖x s - z s‖ = 0 := by nlinarith [norm_nonneg (x s - z s)]
    exact norm_eq_zero.1 this
  exact Filter.mem_of_superset (Ioo_mem_nhdsGT (by linarith : t1 < t1 + ε))
    fun s hs => hzero s ⟨hs.1.le, hs.2.le⟩

end Unique

/-! ## L8: the hypotheses (H1)-(H2) imply `GoodF` (needs the LowerC2 and GammaZero Definitions) -/

section Hyp

lemma goodF_of_convex {f : E → EReal} {m : ℝ} (hlsc : LowerSemicontinuous f)
    (hconv : MoreauProx.Characterization.EConvex f) (hlb : ∀ y, (m : EReal) ≤ f y) :
    GoodF f m where
  lsc := hlsc
  bot y := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hlb y)
  lb := hlb
  semi R := ⟨0, 1, le_rfl, one_pos, fun u _ y _ θ h0 h1 a b ha hb => by
    have hmem := hconv (show (u, a) ∈ {p : E × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} from ha)
      (show (y, b) ∈ {p : E × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} from hb)
      (sub_nonneg.2 h1) h0 (by ring)
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hmem
    have e : (1 - θ) • u + θ • y = u + θ • (y - u) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e] at hmem
    refine hmem.trans (le_of_eq ?_)
    congr 1
    ring⟩

set_option maxHeartbeats 2000000 in
lemma segment_semiconv {φ : E → ℝ} {Dφ : E → (E →L[ℝ] ℝ)} {D2φ : E → (E →L[ℝ] E →L[ℝ] ℝ)}
    {u y : E} {K : ℝ}
    (hφ : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt φ (Dφ (u + θ • (y - u))) (u + θ • (y - u)))
    (hD : ∀ θ ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt Dφ (D2φ (u + θ • (y - u))) (u + θ • (y - u)))
    (hK : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖D2φ (u + θ • (y - u))‖ ≤ K) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    φ (u + θ • (y - u)) ≤ (1 - θ) * φ u + θ * φ y + K / 2 * θ * (1 - θ) * ‖y - u‖ ^ 2 := by
  have hpd : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => u + τ • (y - u)) (y - u) τ := fun τ => by
    simpa using ((hasDerivAt_id τ).smul_const (y - u)).const_add u
  have hg : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ : ℝ => φ (u + τ • (y - u)) + K * ‖y - u‖ ^ 2 / 2 * τ ^ 2)
        (Dφ (u + τ • (y - u)) (y - u) + K * ‖y - u‖ ^ 2 * τ) τ := by
    intro τ hτ
    have h1 := (hφ τ hτ).comp_hasDerivAt τ (hpd τ)
    have h2 := (hasDerivAt_pow 2 τ).const_mul (K * ‖y - u‖ ^ 2 / 2)
    refine (h1.add h2).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have hg' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ : ℝ => Dφ (u + τ • (y - u)) (y - u) + K * ‖y - u‖ ^ 2 * τ)
        (D2φ (u + τ • (y - u)) (y - u) (y - u) + K * ‖y - u‖ ^ 2) τ := by
    intro τ hτ
    have h1 := ((hD τ hτ).comp_hasDerivAt τ (hpd τ)).clm_apply (hasDerivAt_const τ (y - u))
    have h2 := (hasDerivAt_id τ).const_mul (K * ‖y - u‖ ^ 2)
    refine (h1.add h2).congr_deriv ?_
    simp
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun τ : ℝ => φ (u + τ • (y - u)) + K * ‖y - u‖ ^ 2 / 2 * τ ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      (f' := fun τ => Dφ (u + τ • (y - u)) (y - u) + K * ‖y - u‖ ^ 2 * τ)
      (f'' := fun τ => D2φ (u + τ • (y - u)) (y - u) (y - u) + K * ‖y - u‖ ^ 2)
    · exact fun τ hτ => (hg τ hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (hg τ (Set.Ioo_subset_Icc_self hτ)).hasDerivWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (hg' τ (Set.Ioo_subset_Icc_self hτ)).hasDerivWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have h1 := (D2φ (u + τ • (y - u))).le_opNorm₂ (y - u) (y - u)
      have h2 := hK τ (Set.Ioo_subset_Icc_self hτ)
      have h3 : ‖D2φ (u + τ • (y - u)) (y - u) (y - u)‖ ≤ K * ‖y - u‖ ^ 2 := by
        calc _ ≤ ‖D2φ (u + τ • (y - u))‖ * ‖y - u‖ * ‖y - u‖ := h1
          _ ≤ K * ‖y - u‖ * ‖y - u‖ := by gcongr
          _ = K * ‖y - u‖ ^ 2 := by ring
      rw [Real.norm_eq_abs] at h3
      show 0 ≤ D2φ (u + τ • (y - u)) (y - u) (y - u) + K * ‖y - u‖ ^ 2
      linarith [neg_abs_le (D2φ (u + τ • (y - u)) (y - u) (y - u))]
  have := hconv.2 (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    (sub_nonneg.2 hθ.2) hθ.1 (by ring)
  have e2 : u + (y - u) = y := by abel
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, zero_smul, add_zero, one_smul, e2]
    at this
  nlinarith

lemma lowerC2_lsc {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal}
    (hC2 : NonsmoothLojasiewicz.Traj.IsLowerC2 f) (hfin : ∀ y, f y ≠ ⊤) :
    LowerSemicontinuous f := by
  intro x0 c hc
  obtain ⟨U, hUo, hx0U, S, _, _, F, DF, D2F, hFc, hmax, -, -, -⟩ := hC2 x0 (hfin x0)
  obtain ⟨s0, hfs0, -⟩ := hmax x0 hx0U
  have hcont : ContinuousAt (fun x => ((F x s0 : ℝ) : EReal)) x0 := by
    have h1 : ContinuousAt (Function.uncurry F) (x0, s0) :=
      hFc.continuousAt (prod_mem_nhds (hUo.mem_nhds hx0U) Filter.univ_mem)
    have h2 : ContinuousAt (fun x : EuclideanSpace ℝ (Fin n) => (x, s0)) x0 :=
      continuousAt_id.prodMk continuousAt_const
    have h3 : ContinuousAt (fun x => F x s0) x0 :=
      ContinuousAt.comp (g := Function.uncurry F) (f := fun x => (x, s0)) h1 h2
    exact continuous_coe_real_ereal.continuousAt.comp h3
  rw [hfs0] at hc
  filter_upwards [hcont.eventually (lt_mem_nhds hc), hUo.mem_nhds hx0U] with x h1 hxU
  obtain ⟨sx, hfx, hsx⟩ := hmax x hxU
  rw [hfx]
  exact h1.trans_le (EReal.coe_le_coe_iff.2 (hsx s0))

lemma lowerC2_local {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal}
    (hC2 : NonsmoothLojasiewicz.Traj.IsLowerC2 f) (hfin : ∀ y, f y ≠ ⊤)
    (x0 : EuclideanSpace ℝ (Fin n)) :
    ∃ r > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Metric.ball x0 r, ∀ y ∈ Metric.ball x0 r, ∀ θ : ℝ,
      0 ≤ θ → θ ≤ 1 → ∀ a b : ℝ, f u ≤ a → f y ≤ b →
        f (u + θ • (y - u)) ≤ (((1 - θ) * a + θ * b + K * θ * (1 - θ) * ‖y - u‖ ^ 2 : ℝ) : EReal) := by
  obtain ⟨U, hUo, hx0U, S, _, _, F, DF, D2F, hFc, hmax, hder, hDFc, hD2Fc⟩ := hC2 x0 (hfin x0)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo x0 hx0U
  have hrU : Metric.closedBall x0 (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεU
  have hcont : ContinuousOn (Function.uncurry D2F) (Metric.closedBall x0 (ε / 2) ×ˢ Set.univ) :=
    hD2Fc.mono (Set.prod_mono hrU subset_rfl)
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (f := Function.uncurry D2F)
    ((isCompact_closedBall x0 (ε / 2)).prod (isCompact_univ (X := S))) hcont
  refine ⟨ε / 2, by positivity, |C| / 2, by positivity,
    fun u hu y hy θ h0 h1 a b ha hb => ?_⟩
  have hseg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, u + τ • (y - u) ∈ Metric.ball x0 (ε / 2) :=
    fun τ hτ => (convex_ball x0 (ε / 2)).add_smul_sub_mem hu hy hτ
  have hmemU : ∀ τ ∈ Set.Icc (0 : ℝ) 1, u + τ • (y - u) ∈ U :=
    fun τ hτ => hrU (Metric.ball_subset_closedBall (hseg τ hτ))
  obtain ⟨s, hfs, -⟩ := hmax _ (hmemU θ ⟨h0, h1⟩)
  have hsc := segment_semiconv (φ := fun z => F z s) (Dφ := fun z => DF z s)
    (D2φ := fun z => D2F z s) (u := u) (y := y) (K := |C|)
    (fun τ hτ => (hder _ (hmemU τ hτ) s).1) (fun τ hτ => (hder _ (hmemU τ hτ) s).2)
    (fun τ hτ => (hC (_, s) ⟨Metric.ball_subset_closedBall (hseg τ hτ), Set.mem_univ _⟩).trans
      (le_abs_self C)) ⟨h0, h1⟩
  obtain ⟨su, hfu, hsu⟩ := hmax u (hrU (Metric.ball_subset_closedBall hu))
  obtain ⟨sy, hfy, hsy⟩ := hmax y (hrU (Metric.ball_subset_closedBall hy))
  rw [hfu, EReal.coe_le_coe_iff] at ha
  rw [hfy, EReal.coe_le_coe_iff] at hb
  rw [hfs, EReal.coe_le_coe_iff]
  have hu' : (1 - θ) * F u s ≤ (1 - θ) * a :=
    mul_le_mul_of_nonneg_left ((hsu s).trans ha) (sub_nonneg.2 h1)
  have hy' : θ * F y s ≤ θ * b := mul_le_mul_of_nonneg_left ((hsy s).trans hb) h0
  linarith

lemma goodF_of_lowerC2 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal} {m : ℝ}
    (hC2 : NonsmoothLojasiewicz.Traj.IsLowerC2 f) (hfin : ∀ y, f y ≠ ⊤)
    (hlb : ∀ y, (m : EReal) ≤ f y) : GoodF f m where
  lsc := lowerC2_lsc hC2 hfin
  bot y := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hlb y)
  lb := hlb
  semi R := by
    choose r hr K hK hloc using lowerC2_local hC2 hfin
    obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).elim_finite_subcover
      (fun x => Metric.ball x (r x)) (fun x => Metric.isOpen_ball)
      (fun x _ => Set.mem_iUnion.2 ⟨x, Metric.mem_ball_self (hr x)⟩)
    obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
      (c := fun i : t => Metric.ball (i : EuclideanSpace ℝ (Fin n)) (r i))
      (fun i => Metric.isOpen_ball) (by
        intro x hx
        have := ht hx
        simp only [Set.mem_iUnion] at this ⊢
        obtain ⟨i, hi, hxi⟩ := this
        exact ⟨⟨i, hi⟩, hxi⟩)
    refine ⟨∑ i ∈ t, K i, δ / 2, Finset.sum_nonneg fun i _ => hK i, by positivity, ?_⟩
    intro u hu y hy θ h0 h1 a b ha hb
    obtain ⟨⟨i, hi⟩, hball⟩ := hleb u hu
    have huB : u ∈ Metric.ball i (r i) := hball (Metric.mem_ball_self hδ)
    have hyB : y ∈ Metric.ball i (r i) :=
      hball (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
    refine (hloc i u huB y hyB θ h0 h1 a b ha hb).trans (EReal.coe_le_coe_iff.2 ?_)
    have hKi : K i ≤ ∑ j ∈ t, K j := Finset.single_le_sum (fun j _ => hK j) hi
    have hnn : 0 ≤ θ * (1 - θ) * ‖y - u‖ ^ 2 := by
      have := sub_nonneg.2 h1; positivity
    nlinarith [mul_le_mul_of_nonneg_right hKi hnn]

end Hyp

end TrajLib

-- Corollary 4.1(iii): maximal extension on `[0, ∞)` with square-integrable velocity.
open MeasureTheory Filter Topology ENNReal NonsmoothLojasiewicz.Traj in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsTrajectory f x T) :
    ∃ xhat : ℝ → EuclideanSpace ℝ (Fin n),
      (∀ t ∈ timeDom T, xhat t = x t) ∧
      IsMaximalTrajectory f xhat ⊤ ∧
      ∫⁻ t in Set.Ioi (0 : ℝ), ‖deriv xhat t‖ₑ ^ 2 < ⊤ := by
  obtain ⟨-, m, hm⟩ := hH2
  have hf : TrajLib.GoodF f m := by
    rcases hH1 with ⟨hlsc, hconv⟩ | ⟨hC2, hfin⟩
    · exact TrajLib.goodF_of_convex hlsc hconv hm
    · exact TrajLib.goodF_of_lowerC2 hC2 hfin hm
  have hT0 : ENNReal.ofReal 0 < T := by rw [ENNReal.ofReal_zero]; exact hx.1
  obtain ⟨w, hw⟩ := hx.2.2.2 0 le_rfl hT0
  have hx0 : f (x 0) ≠ ⊤ := by
    obtain ⟨h, -⟩ := hw
    exact h
  obtain ⟨z, hz0, hzle, hzT⟩ := TrajLib.exists_limit_curve hf hx0 hw
  have hfin : ∀ t, f (z t) ≠ ⊤ := fun t => ne_top_of_le_ne_top hx0 (hzle t)
  have hz : ∀ T : ℝ, 0 ≤ T → ∃ L ρ δ : ℝ, TrajLib.LeviData f z T L ρ δ := hzT
  have hae := TrajLib.ae_hasDeriv_subgrad hf.bot hfin hz
  refine ⟨z, fun t ht => ?_, ⟨⟨by simp, fun b hb _ => ?_, ?_, fun t ht _ => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨L, ρ, δ, hD⟩ := hz t ht.1
    have h := TrajLib.traj_unique hf (hx.2.1 t ht.1 ht.2) (hD.ac ht.1)
      (hx.2.2.1.mono fun s hs hs0 hst =>
        hs hs0 ((ENNReal.ofReal_le_ofReal hst.le).trans_lt ht.2))
      (hae.mono fun s hs hs0 _ => hs hs0) hz0.symm t ⟨ht.1, le_rfl⟩
    exact h.symm
  · obtain ⟨L, ρ, δ, hD⟩ := hz b hb
    exact hD.ac hb
  · exact hae.mono fun t h ht _ => h ht
  · rcases ht.lt_or_eq with htpos | h0
    · obtain ⟨L, ρ, δ, hD⟩ := hz t ht
      exact hD.subdiff_nonempty hf.bot htpos le_rfl (hfin t)
    · rw [← h0, hz0]
      exact ⟨w, hw⟩
  · rintro ⟨T', hT', -⟩
    exact not_top_lt hT'
  · exact (TrajLib.lintegral_speed_le hf.bot hfin hm hz).trans_lt ENNReal.ofReal_lt_top
