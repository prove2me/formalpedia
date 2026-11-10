-- Prove2me | solution 1 for GraphConvSubgrad.StatConc.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T01:53:21.667113+00:00
-- url     : https://prove2.me/submissions/bc16a86e-c745-4636-937c-40097309c9cd

import Mathlib
import Definitions.Def_GraphConvSubgrad_StatConc_Setting

namespace GraphConvSubgrad.StatConc.Lib

section S_M_point
set_option autoImplicit false

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Three-point inequality for a Bregman proximal point (no sign condition on `ρ̄ - ρ`):
if `g + ρ Φ` is convex on `dom g ∩ dom Φ`, `Φ` is differentiable at the prox point `p`, then
`g(u) + ρ̄ D(u,y) ≥ g(p) + ρ̄ D(p,y) + (ρ̄ - ρ) D(u,p)`. -/
theorem three_point (Φ g : ExtFn E) (ρ rhoBar : ℝ) (y p u : E)
    (hw : WeaklyConvexRel Φ g ρ) (hp : p ∈ proxSet Φ g rhoBar y)
    (hd : DifferentiableAt ℝ Φ.val p) (hu : u ∈ g.dom ∩ Φ.dom) :
    g.val p + rhoBar * bregman Φ p y + (rhoBar - ρ) * bregman Φ u p
      ≤ g.val u + rhoBar * bregman Φ u y := by
  obtain ⟨hpK, hmin⟩ := hp
  set K := g.dom ∩ Φ.dom
  have hK : Convex ℝ K := hw.1
  -- line through p towards u
  set v : ℝ → E := fun t => p + t • (u - p) with hv
  have hvK : ∀ t ∈ Set.Ioc (0:ℝ) 1, v t ∈ K := by
    intro t ht
    have : v t = (1 - t) • p + t • u := by
      simp only [hv]; rw [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact hK hpK hu (by linarith [ht.2]) ht.1.le (by ring)
  -- derivative of Φ along the line
  have hline : HasDerivAt v ((1:ℝ) • (u - p)) 0 :=
    ((hasDerivAt_id (0:ℝ)).smul_const (u - p)).const_add p
  have hΦline : HasDerivAt (fun t => Φ.val (v t)) (fderiv ℝ Φ.val p (u - p)) 0 := by
    have h0 : v 0 = p := by simp [hv]
    have hd' : HasFDerivAt Φ.val (fderiv ℝ Φ.val p) (v 0) := by rw [h0]; exact hd.hasFDerivAt
    have := hd'.comp_hasDerivAt (0:ℝ) hline
    rw [one_smul] at this
    exact this
  have hslope := hΦline.tendsto_slope_zero_right
  -- key inequality for t ∈ (0,1]
  set A := (g.val u + ρ * Φ.val u) - (g.val p + ρ * Φ.val p)
  set B := rhoBar * fderiv ℝ Φ.val y (u - p)
  have key : ∀ t ∈ Set.Ioc (0:ℝ) 1,
      0 ≤ A + (rhoBar - ρ) * (t⁻¹ • (Φ.val (v t) - Φ.val p)) - B := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hmin' := hmin (hvK t ht)
    simp only [Set.mem_ofPred_eq] at hmin'
    have hconv := hw.2 hpK hu (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    have hvt : (1 - t) • p + t • u = v t := by
      simp only [hv]; rw [smul_sub, sub_smul, one_smul]; abel
    rw [hvt] at hconv
    simp only [smul_eq_mul] at hconv
    unfold bregman at hmin'
    have hlin : fderiv ℝ Φ.val y (v t - y) = fderiv ℝ Φ.val y (p - y)
        + t * fderiv ℝ Φ.val y (u - p) := by
      have : v t - y = (p - y) + t • (u - p) := by simp only [hv]; abel
      rw [this, map_add, map_smul, smul_eq_mul]
    rw [hlin] at hmin'
    -- multiply target by t
    have hgoal : 0 ≤ t * (A + (rhoBar - ρ) * (t⁻¹ * (Φ.val (v t) - Φ.val p)) - B) := by
      have e : t * (A + (rhoBar - ρ) * (t⁻¹ * (Φ.val (v t) - Φ.val p)) - B)
          = t * A + (rhoBar - ρ) * (Φ.val (v t) - Φ.val p) - t * B := by
        field_simp
      rw [e]
      simp only [A, B]
      nlinarith [hmin', hconv]
    simp only [smul_eq_mul]
    exact (mul_nonneg_iff_of_pos_left ht0).1 hgoal
  have hlim : Tendsto (fun t : ℝ => A + (rhoBar - ρ) * (t⁻¹ • (Φ.val (v t) - Φ.val p)) - B)
      (𝓝[>] 0) (𝓝 (A + (rhoBar - ρ) * fderiv ℝ Φ.val p (u - p) - B)) := by
    have h0 : v 0 = p := by simp [hv]
    have hs : Tendsto (fun t : ℝ => t⁻¹ • (Φ.val (v t) - Φ.val p)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ Φ.val p (u - p))) := by
      have := hslope
      simp only [zero_add, h0] at this
      exact this
    exact ((hs.const_mul (rhoBar - ρ)).const_add A).sub_const B
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
      0 ≤ A + (rhoBar - ρ) * (t⁻¹ • (Φ.val (v t) - Φ.val p)) - B := by
    have : Set.Ioc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioc_mem_nhdsGT (by norm_num)
    filter_upwards [this] with t ht using key t ht
  have hfin := ge_of_tendsto hlim hev
  simp only [A, B] at hfin
  unfold bregman
  have e2 : fderiv ℝ Φ.val y (u - y) = fderiv ℝ Φ.val y (p - y) + fderiv ℝ Φ.val y (u - p) := by
    rw [← map_add]; congr 1; abel
  rw [e2]
  nlinarith [hfin]

/-- Stability of Bregman proximal points: for two functions with a common domain, two centres,
both `ρ`-weakly convex relative to `Φ`, with prox points where `Φ` is differentiable,
`(ρ̄ - ρ) Dsym(p₁,p₂) ≤ (g₁-g₂)(p₂) - (g₁-g₂)(p₁) + ρ̄ (∇Φ(y₂) - ∇Φ(y₁))(p₂ - p₁)`. -/
theorem prox_stability (Φ g₁ g₂ : ExtFn E) (ρ rhoBar : ℝ) (y₁ y₂ p₁ p₂ : E)
    (hdom : g₁.dom = g₂.dom)
    (hw₁ : WeaklyConvexRel Φ g₁ ρ) (hw₂ : WeaklyConvexRel Φ g₂ ρ)
    (hp₁ : p₁ ∈ proxSet Φ g₁ rhoBar y₁) (hp₂ : p₂ ∈ proxSet Φ g₂ rhoBar y₂)
    (hd₁ : DifferentiableAt ℝ Φ.val p₁) (hd₂ : DifferentiableAt ℝ Φ.val p₂) :
    (rhoBar - ρ) * bregmanSym Φ p₁ p₂
      ≤ (g₁.val p₂ - g₂.val p₂) - (g₁.val p₁ - g₂.val p₁)
        + rhoBar * (fderiv ℝ Φ.val y₂ - fderiv ℝ Φ.val y₁) (p₂ - p₁) := by
  have hp₂K : p₂ ∈ g₁.dom ∩ Φ.dom := by rw [hdom]; exact hp₂.1
  have hp₁K : p₁ ∈ g₂.dom ∩ Φ.dom := by rw [← hdom]; exact hp₁.1
  have h1 := three_point Φ g₁ ρ rhoBar y₁ p₁ p₂ hw₁ hp₁ hd₁ hp₂K
  have h2 := three_point Φ g₂ ρ rhoBar y₂ p₂ p₁ hw₂ hp₂ hd₂ hp₁K
  unfold bregmanSym
  unfold bregman at h1 h2 ⊢
  have e1 : fderiv ℝ Φ.val y₁ (p₂ - y₁) = fderiv ℝ Φ.val y₁ (p₁ - y₁)
      + fderiv ℝ Φ.val y₁ (p₂ - p₁) := by rw [← map_add]; congr 1; abel
  have e2 : fderiv ℝ Φ.val y₂ (p₁ - y₂) = fderiv ℝ Φ.val y₂ (p₂ - y₂)
      - fderiv ℝ Φ.val y₂ (p₂ - p₁) := by rw [← map_sub]; congr 1; abel
  have e3 : fderiv ℝ Φ.val p₂ (p₁ - p₂) = - fderiv ℝ Φ.val p₂ (p₂ - p₁) := by
    rw [← map_neg]; congr 1; abel
  rw [e1] at h1; rw [e2] at h2
  rw [ContinuousLinearMap.sub_apply]
  nlinarith [h1, h2]

/-- Net perturbation of a Bregman prox point: moving the centre from `y` to `t` with
`‖∇Φ(y) - ∇Φ(t)‖ ≤ δ` moves the prox point by at most `ρ̄ δ / (α (ρ̄ - ρ))`. -/
theorem net_perturb (Φ g : ExtFn E) (ρ rhoBar α δ : ℝ) (y t p q : E)
    (hw : WeaklyConvexRel Φ g ρ)
    (hp : p ∈ proxSet Φ g rhoBar y) (hq : q ∈ proxSet Φ g rhoBar t)
    (hdp : DifferentiableAt ℝ Φ.val p) (hdq : DifferentiableAt ℝ Φ.val q)
    (hsc₁ : α / 2 * ‖q - p‖ ^ 2 ≤ bregman Φ p q) (hsc₂ : α / 2 * ‖p - q‖ ^ 2 ≤ bregman Φ q p)
    (hα : 0 < α) (hρ : ρ < rhoBar) (hrb : 0 ≤ rhoBar)
    (hnet : ‖fderiv ℝ Φ.val y - fderiv ℝ Φ.val t‖ ≤ δ) :
    ‖p - q‖ ≤ rhoBar * δ / (α * (rhoBar - ρ)) := by
  have hst := prox_stability Φ g g ρ rhoBar y t p q rfl hw hw hp hq hdp hdq
  simp only [sub_self, zero_add] at hst
  have hnorm : (fderiv ℝ Φ.val t - fderiv ℝ Φ.val y) (q - p) ≤ δ * ‖p - q‖ := by
    calc (fderiv ℝ Φ.val t - fderiv ℝ Φ.val y) (q - p)
        ≤ ‖(fderiv ℝ Φ.val t - fderiv ℝ Φ.val y) (q - p)‖ := le_abs_self _ |>.trans (le_of_eq (Real.norm_eq_abs _).symm)
      _ ≤ ‖fderiv ℝ Φ.val t - fderiv ℝ Φ.val y‖ * ‖q - p‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ δ * ‖p - q‖ := by
        rw [norm_sub_rev (fderiv ℝ Φ.val t), norm_sub_rev q]
        exact mul_le_mul_of_nonneg_right hnet (norm_nonneg _)
  have hqp : ‖q - p‖ = ‖p - q‖ := norm_sub_rev _ _
  rw [hqp] at hsc₁
  have hsym : α * ‖p - q‖ ^ 2 ≤ bregmanSym Φ p q := by unfold bregmanSym; linarith
  have hgap : 0 < rhoBar - ρ := by linarith
  have key : (rhoBar - ρ) * (α * ‖p - q‖ ^ 2) ≤ rhoBar * (δ * ‖p - q‖) := by
    have h1 := mul_le_mul_of_nonneg_left hsym hgap.le
    have h2 := mul_le_mul_of_nonneg_left hnorm hrb
    linarith
  rcases (norm_nonneg (p - q)).eq_or_lt with h0 | hpos
  · rw [← h0]
    have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hnet
    positivity
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [key, hpos]

/-- Real-number step: `(ρ̄ - ρ) D ≤ K √D`, `D ≥ 0`, `ρ < ρ̄` give `√D ≤ K / (ρ̄ - ρ)`. -/
theorem sqrt_le_of_quad (D K gap : ℝ) (hD : 0 ≤ D) (hgap : 0 < gap) (hK : 0 ≤ K)
    (h : gap * D ≤ K * Real.sqrt D) : Real.sqrt D ≤ K / gap := by
  rw [le_div_iff₀ hgap]
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg D
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  · nlinarith

/-- Replace-one identity for the empirical risk. -/
theorem empRisk_update {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (r : ExtFn E) (f : E → Ω → ℝ)
    (S : Fin m → Ω) (i : Fin m) (z' : Ω) (u : E) :
    (empRisk r f S).val u - (empRisk r f (Function.update S i z')).val u
      = (1 / (m : ℝ)) * (f u (S i) - f u z') := by
  simp only [empRisk]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h : ∑ j ∈ Finset.univ.erase i, f u (Function.update S i z' j)
      = ∑ j ∈ Finset.univ.erase i, f u (S j) :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [h, Function.update_self]
  ring

/-- Gradient inequality for a convex function at a point of differentiability. -/
theorem convex_fderiv_le (Φ : E → ℝ) (s : Set E) (hc : ConvexOn ℝ s Φ) (x z : E)
    (hx : x ∈ s) (hz : z ∈ s) (hd : DifferentiableAt ℝ Φ x) :
    Φ x + fderiv ℝ Φ x (z - x) ≤ Φ z := by
  set v : ℝ → E := fun t => x + t • (z - x) with hv
  have h0 : v 0 = x := by simp [hv]
  have hline : HasDerivAt v ((1:ℝ) • (z - x)) 0 :=
    ((hasDerivAt_id (0:ℝ)).smul_const (z - x)).const_add x
  have hd' : HasFDerivAt Φ (fderiv ℝ Φ x) (v 0) := by rw [h0]; exact hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0:ℝ) hline
  rw [one_smul] at h1
  have hΦline : HasDerivAt (fun t => Φ (v t)) (fderiv ℝ Φ x (z - x)) 0 := h1
  have hs := hΦline.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (Φ (v (0 + t)) - Φ (v 0)) ≤ Φ z - Φ x := by
    filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    rw [zero_add, h0, smul_eq_mul]
    have hc' := hc.2 hx hz (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1.le (by ring)
    have hvt : (1 - t) • x + t • z = v t := by
      simp only [hv]; rw [smul_sub, sub_smul, one_smul]; abel
    rw [hvt, smul_eq_mul, smul_eq_mul] at hc'
    rw [inv_mul_le_iff₀ ht.1]; nlinarith
  have := le_of_tendsto hs hev
  linarith

/-- A linear functional bounded above by `B` on the closed `r`-ball has norm at most `B / r`. -/
theorem opNorm_le_of_ball_bound (φ : E →L[ℝ] ℝ) (r B : ℝ) (hr : 0 < r)
    (h : ∀ w : E, ‖w‖ ≤ r → φ w ≤ B) : ‖φ‖ ≤ B / r := by
  have hB : 0 ≤ B := by simpa using h 0 (by simp; exact hr.le)
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hB hr.le)
  intro e
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have hne : 0 < ‖e‖ := norm_pos_iff.2 he
  set c := r / ‖e‖ with hcdef
  have hc : 0 < c := div_pos hr hne
  have hce : ‖c • e‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hc.le, hcdef]; field_simp
  have h1 := h (c • e) hce.le
  have h2 := h (-(c • e)) (by rw [norm_neg]; exact hce.le)
  rw [map_smul, smul_eq_mul] at h1
  rw [map_neg, map_smul, smul_eq_mul] at h2
  have key : |φ e| * c ≤ B := by
    rcases abs_cases (φ e) with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] <;> nlinarith
  have : B / r * ‖e‖ = B / c := by rw [hcdef]; field_simp
  rw [Real.norm_eq_abs, this, le_div_iff₀ hc]
  exact key

/-- Rockafellar Lemma 26.2 (form used here): at a point `p ∈ dom Φ \ int dom Φ` of a Legendre
function, the slope of `Φ` along the segment towards an interior point `u` is unbounded below. -/
theorem frontier_slope [FiniteDimensional ℝ E] (Φ : ExtFn E) (hL : IsLegendre Φ) (p u : E)
    (hp : p ∈ Φ.dom) (hpi : p ∉ interior Φ.dom) (hu : u ∈ interior Φ.dom) (M : ℝ) :
    ∃ t ∈ Set.Ioc (0:ℝ) 1, Φ.val (p + t • (u - p)) - Φ.val p < -(M * t) := by
  by_contra hcon
  push_neg at hcon
  have hconv : ConvexOn ℝ Φ.dom Φ.val := hL.strictConvex.convexOn
  have hK : Convex ℝ Φ.dom := hconv.1
  have hpc : p ∈ closure Φ.dom := subset_closure hp
  have hfr : p ∈ frontier Φ.dom := ⟨hpc, hpi⟩
  set v : ℝ → E := fun t => p + t • (u - p) with hv
  have hvint : ∀ t ∈ Set.Ioc (0:ℝ) 1, v t ∈ interior Φ.dom :=
    fun t ht => hK.add_smul_sub_mem_interior' hpc hu ht
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u hu
  have hε2 : 0 < ε / 2 := by linarith
  have hcb : Metric.closedBall u (ε / 2) ⊆ interior Φ.dom := fun z hz => by
    apply hball; rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz; linarith
  have hcont : ContinuousOn Φ.val (Metric.closedBall u (ε / 2)) :=
    (hL.differentiableOn.continuousOn).mono hcb
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall u (ε / 2)).bddAbove_image hcont
  set B := C0 - Φ.val p + 2 * |M| with hBdef
  have hbound : ∀ t ∈ Set.Ioc (0:ℝ) 1, ‖fderiv ℝ Φ.val (v t)‖ ≤ B / (ε / 2) := by
    intro t ht
    have hvt := hvint t ht
    have hdv : DifferentiableAt ℝ Φ.val (v t) :=
      (hL.differentiableOn _ hvt).differentiableAt (isOpen_interior.mem_nhds hvt)
    have hvdom : v t ∈ Φ.dom := interior_subset hvt
    have hzp := convex_fderiv_le Φ.val Φ.dom hconv (v t) p hvdom hp hdv
    have hpv : p - v t = (-t) • (u - p) := by simp only [hv]; rw [neg_smul]; abel
    rw [hpv, map_smul, smul_eq_mul] at hzp
    have hH := hcon t ht
    have hD1 : -M ≤ fderiv ℝ Φ.val (v t) (u - p) := by
      have : t * (-M) ≤ t * fderiv ℝ Φ.val (v t) (u - p) := by nlinarith
      exact le_of_mul_le_mul_left this ht.1
    have hMt : M * t ≤ |M| := by
      calc M * t ≤ |M| * t := mul_le_mul_of_nonneg_right (le_abs_self M) ht.1.le
        _ ≤ |M| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg M)
        _ = |M| := mul_one _
    have hΦv : Φ.val p - |M| ≤ Φ.val (v t) := by linarith
    apply opNorm_le_of_ball_bound _ (ε / 2) B hε2
    intro w hw
    have hzw : u + w ∈ Metric.closedBall u (ε / 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm]; simpa using hw
    have hzdom : u + w ∈ Φ.dom := interior_subset (hcb hzw)
    have hle := convex_fderiv_le Φ.val Φ.dom hconv (v t) (u + w) hvdom hzdom hdv
    have hsplit : u + w - v t = (1 - t) • (u - p) + w := by
      simp only [hv]; rw [sub_smul, one_smul]; abel
    rw [hsplit, map_add, map_smul, smul_eq_mul] at hle
    have hCz : Φ.val (u + w) ≤ C0 := hC0 ⟨u + w, hzw, rfl⟩
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    have hM' : -M ≤ |M| := neg_le_abs M
    have hprod : (1 - t) * (-M) ≤ (1 - t) * fderiv ℝ Φ.val (v t) (u - p) :=
      mul_le_mul_of_nonneg_left hD1 h1t
    have hprod2 : (1 - t) * M ≤ |M| := by
      calc (1 - t) * M ≤ (1 - t) * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) h1t
        _ ≤ 1 * |M| := mul_le_mul_of_nonneg_right (by linarith [ht.1]) (abs_nonneg M)
        _ = |M| := one_mul _
    rw [hBdef]
    linarith
  have hess := hL.essSmooth p hfr
  have h0 : v 0 = p := by simp [hv]
  have hvt : Tendsto v (𝓝[>] (0:ℝ)) (𝓝[interior Φ.dom] p) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : Continuous v := by simp only [hv]; fun_prop
      have := hc.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht using hvint t ht
  have htend := hess.comp hvt
  have hev1 := htend.eventually_gt_atTop (B / (ε / 2))
  have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioc (0:ℝ) 1 := Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨t, h1, h2⟩ := (hev1.and hev2).exists
  exact absurd (hbound t h2) (not_le.2 h1)

/-- Minimality of a prox point along the segment towards `u` (exact convexity bookkeeping). -/
theorem prox_line (Φ g : ExtFn E) (ρ rhoBar : ℝ) (y p u : E)
    (hw : WeaklyConvexRel Φ g ρ) (hp : p ∈ proxSet Φ g rhoBar y) (hu : u ∈ g.dom ∩ Φ.dom)
    (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
    0 ≤ t * ((g.val u + ρ * Φ.val u) - (g.val p + ρ * Φ.val p))
      + (rhoBar - ρ) * (Φ.val (p + t • (u - p)) - Φ.val p)
      - t * (rhoBar * fderiv ℝ Φ.val y (u - p)) := by
  obtain ⟨hpK, hmin⟩ := hp
  have hK : Convex ℝ (g.dom ∩ Φ.dom) := hw.1
  have hvt : (1 - t) • p + t • u = p + t • (u - p) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  have hvK : p + t • (u - p) ∈ g.dom ∩ Φ.dom := by
    rw [← hvt]; exact hK hpK hu (by linarith [ht.2]) ht.1.le (by ring)
  have hmin' := hmin hvK
  simp only [Set.mem_ofPred_eq] at hmin'
  have hconv := hw.2 hpK hu (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1.le (by ring)
  rw [hvt] at hconv
  simp only [smul_eq_mul] at hconv
  unfold bregman at hmin'
  have hlin : fderiv ℝ Φ.val y (p + t • (u - p) - y) = fderiv ℝ Φ.val y (p - y)
      + t * fderiv ℝ Φ.val y (u - p) := by
    have : p + t • (u - p) - y = (p - y) + t • (u - p) := by abel
    rw [this, map_add, map_smul, smul_eq_mul]
  rw [hlin] at hmin'
  nlinarith [hmin', hconv]

/-- D1: Bregman prox points of a Legendre function lie in `int (dom Φ)`, provided the domain of
`g` meets `int (dom Φ)` and `ρ < ρ̄`. -/
theorem prox_interior [FiniteDimensional ℝ E] (Φ g : ExtFn E) (ρ rhoBar : ℝ) (y p u0 : E)
    (hL : IsLegendre Φ) (hw : WeaklyConvexRel Φ g ρ) (hρ : ρ < rhoBar)
    (hp : p ∈ proxSet Φ g rhoBar y) (hu0 : u0 ∈ g.dom) (hu0i : u0 ∈ interior Φ.dom) :
    p ∈ interior Φ.dom := by
  by_contra hpi
  have hgap : 0 < rhoBar - ρ := by linarith
  set A := (g.val u0 + ρ * Φ.val u0) - (g.val p + ρ * Φ.val p) with hA
  set B := rhoBar * fderiv ℝ Φ.val y (u0 - p) with hB
  obtain ⟨t, ht, hlt⟩ := frontier_slope Φ hL p u0 hp.1.2 hpi hu0i ((|A| + |B| + 1) / (rhoBar - ρ))
  have hu0K : u0 ∈ g.dom ∩ Φ.dom := ⟨hu0, interior_subset hu0i⟩
  have hline := prox_line Φ g ρ rhoBar y p u0 hw hp hu0K t ht
  rw [← hA, ← hB] at hline
  have hmul : (rhoBar - ρ) * (Φ.val (p + t • (u0 - p)) - Φ.val p)
      < -((|A| + |B| + 1) * t) := by
    have := mul_lt_mul_of_pos_left hlt hgap
    have e : (rhoBar - ρ) * -((|A| + |B| + 1) / (rhoBar - ρ) * t) = -((|A| + |B| + 1) * t) := by
      field_simp
    linarith
  have ht0 := ht.1
  have hAa : t * A ≤ t * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) ht0.le
  have hBb : -(t * B) ≤ t * |B| := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs B) ht0.le; linarith
  nlinarith

/-- Replace-one stability of the empirical prox (both proxes at the same centre). -/
theorem replace_one {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m) (Φ r : ExtFn E)
    (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ rhoBar α : ℝ) (hα : 0 < α) (hρ : ρ < rhoBar)
    (hsc : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom,
      α / 2 * ‖y - x‖ ^ 2 ≤ bregman Φ x y)
    (hlip : ∀ x ∈ interior Φ.dom ∩ r.dom, ∀ y ∈ interior Φ.dom ∩ r.dom, ∀ z,
      |f x z - f y z| ≤ L z * Real.sqrt (bregmanSym Φ x y))
    (hL0 : ∀ z, 0 ≤ L z) (S : Fin m → Ω) (i : Fin m) (z : Ω) (t p₁ p₂ : E)
    (hw₁ : WeaklyConvexRel Φ (empRisk r f S) ρ)
    (hw₂ : WeaklyConvexRel Φ (empRisk r f (Function.update S i z)) ρ)
    (hp₁ : p₁ ∈ proxSet Φ (empRisk r f S) rhoBar t)
    (hp₂ : p₂ ∈ proxSet Φ (empRisk r f (Function.update S i z)) rhoBar t)
    (hi₁ : p₁ ∈ interior Φ.dom) (hi₂ : p₂ ∈ interior Φ.dom)
    (hdiff : DifferentiableOn ℝ Φ.val (interior Φ.dom)) :
    ‖p₁ - p₂‖ ≤ 1 / (Real.sqrt α * m * (rhoBar - ρ)) * (L (S i) + L z) := by
  have hr₁ : p₁ ∈ r.dom := hp₁.1.1
  have hr₂ : p₂ ∈ r.dom := hp₂.1.1
  have hd₁ : DifferentiableAt ℝ Φ.val p₁ :=
    (hdiff p₁ hi₁).differentiableAt (isOpen_interior.mem_nhds hi₁)
  have hd₂ : DifferentiableAt ℝ Φ.val p₂ :=
    (hdiff p₂ hi₂).differentiableAt (isOpen_interior.mem_nhds hi₂)
  have hst := prox_stability Φ (empRisk r f S) (empRisk r f (Function.update S i z)) ρ rhoBar t t p₁ p₂ rfl hw₁ hw₂ hp₁ hp₂ hd₁ hd₂
  simp only [sub_self, ContinuousLinearMap.zero_apply, mul_zero, add_zero] at hst
  rw [empRisk_update, empRisk_update] at hst
  have hsym : bregmanSym Φ p₂ p₁ = bregmanSym Φ p₁ p₂ := by unfold bregmanSym; ring
  have l1 := hlip p₂ ⟨hi₂, hr₂⟩ p₁ ⟨hi₁, hr₁⟩ (S i)
  have l2 := hlip p₁ ⟨hi₁, hr₁⟩ p₂ ⟨hi₂, hr₂⟩ z
  rw [hsym] at l1
  have hsc1 := hsc p₁ ⟨hr₁, hi₁⟩ p₂ ⟨hr₂, hi₂⟩
  have hsc2 := hsc p₂ ⟨hr₂, hi₂⟩ p₁ ⟨hr₁, hi₁⟩
  have hn : ‖p₂ - p₁‖ = ‖p₁ - p₂‖ := norm_sub_rev _ _
  rw [hn] at hsc1
  have hD : α * ‖p₁ - p₂‖ ^ 2 ≤ bregmanSym Φ p₁ p₂ := by unfold bregmanSym; linarith
  have hD0 : 0 ≤ bregmanSym Φ p₁ p₂ := le_trans (by positivity) hD
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hgap : 0 < rhoBar - ρ := sub_pos.mpr hρ
  have hsa : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have a1 := abs_le.mp l1
  have a2 := abs_le.mp l2
  have hq : (rhoBar - ρ) * bregmanSym Φ p₁ p₂
      ≤ ((L (S i) + L z) / m) * Real.sqrt (bregmanSym Φ p₁ p₂) := by
    have e : 1 / (m : ℝ) * (f p₂ (S i) - f p₂ z) - 1 / (m : ℝ) * (f p₁ (S i) - f p₁ z)
        = (1 / (m : ℝ)) * ((f p₂ (S i) - f p₁ (S i)) + (f p₁ z - f p₂ z)) := by ring
    rw [e] at hst
    calc _ ≤ _ := hst
      _ ≤ (1 / (m : ℝ)) * (L (S i) * Real.sqrt (bregmanSym Φ p₁ p₂)
            + L z * Real.sqrt (bregmanSym Φ p₁ p₂)) := by
          gcongr <;> linarith [a1.2, a2.2]
      _ = _ := by ring
  have hs := sqrt_le_of_quad _ _ _ hD0 hgap (div_nonneg (add_nonneg (hL0 _) (hL0 _)) hmR.le) hq
  have h3 : Real.sqrt α * ‖p₁ - p₂‖ ≤ Real.sqrt (bregmanSym Φ p₁ p₂) := by
    rw [← Real.sqrt_sq (norm_nonneg (p₁ - p₂)), ← Real.sqrt_mul hα.le]
    exact Real.sqrt_le_sqrt hD
  calc ‖p₁ - p₂‖ = (Real.sqrt α * ‖p₁ - p₂‖) / Real.sqrt α := by
        rw [mul_div_cancel_left₀ _ hsa.ne']
    _ ≤ ((L (S i) + L z) / m / (rhoBar - ρ)) / Real.sqrt α := by gcongr; linarith
    _ = _ := by
      have h1 := hgap.ne'; have h2 := hsa.ne'; have h3 := hmR.ne'
      field_simp <;> ring

/-! ## L_cover (session 6): net covering step, good-set nullity, interior base point. -/

theorem cover_step [FiniteDimensional ℝ E] (Φ g₁ g₂ : ExtFn E) (R : Set E) (ρ rhoBar α δ thr : ℝ)
    (u0 : E) (hL : IsLegendre Φ) (hw₁ : WeaklyConvexRel Φ g₁ ρ) (hw₂ : WeaklyConvexRel Φ g₂ ρ)
    (hρ : ρ < rhoBar) (hrb : 0 ≤ rhoBar) (hα : 0 < α)
    (h₁ : g₁.dom = R) (h₂ : g₂.dom = R) (hu0 : u0 ∈ R) (hu0i : u0 ∈ interior Φ.dom)
    (hsc : ∀ x ∈ R ∩ interior Φ.dom, ∀ y ∈ R ∩ interior Φ.dom,
      α / 2 * ‖y - x‖ ^ 2 ≤ bregman Φ x y)
    (y t a b p q : E)
    (ha : a ∈ proxSet Φ g₁ rhoBar y) (hb : b ∈ proxSet Φ g₂ rhoBar y)
    (hp : p ∈ proxSet Φ g₁ rhoBar t) (hq : q ∈ proxSet Φ g₂ rhoBar t)
    (hnet : ‖fderiv ℝ Φ.val y - fderiv ℝ Φ.val t‖ ≤ δ)
    (hlt : thr + 2 * rhoBar * δ / (α * (rhoBar - ρ)) < ‖a - b‖) :
    thr < ‖p - q‖ := by
  have hu1 : u0 ∈ g₁.dom := by rw [h₁]; exact hu0
  have hu2 : u0 ∈ g₂.dom := by rw [h₂]; exact hu0
  have hai := prox_interior Φ g₁ ρ rhoBar y a u0 hL hw₁ hρ ha hu1 hu0i
  have hbi := prox_interior Φ g₂ ρ rhoBar y b u0 hL hw₂ hρ hb hu2 hu0i
  have hpi := prox_interior Φ g₁ ρ rhoBar t p u0 hL hw₁ hρ hp hu1 hu0i
  have hqi := prox_interior Φ g₂ ρ rhoBar t q u0 hL hw₂ hρ hq hu2 hu0i
  have hd : ∀ x ∈ interior Φ.dom, DifferentiableAt ℝ Φ.val x := fun x hx =>
    (hL.differentiableOn x hx).differentiableAt (isOpen_interior.mem_nhds hx)
  have haR : a ∈ R := by rw [← h₁]; exact ha.1.1
  have hbR : b ∈ R := by rw [← h₂]; exact hb.1.1
  have hpR : p ∈ R := by rw [← h₁]; exact hp.1.1
  have hqR : q ∈ R := by rw [← h₂]; exact hq.1.1
  have e1 := net_perturb Φ g₁ ρ rhoBar α δ y t a p hw₁ ha hp (hd a hai) (hd p hpi)
    (hsc a ⟨haR, hai⟩ p ⟨hpR, hpi⟩) (hsc p ⟨hpR, hpi⟩ a ⟨haR, hai⟩) hα hρ hrb hnet
  have e2 := net_perturb Φ g₂ ρ rhoBar α δ y t b q hw₂ hb hq (hd b hbi) (hd q hqi)
    (hsc b ⟨hbR, hbi⟩ q ⟨hqR, hqi⟩) (hsc q ⟨hqR, hqi⟩ b ⟨hbR, hbi⟩) hα hρ hrb hnet
  have htri : ‖a - b‖ ≤ ‖a - p‖ + ‖p - q‖ + ‖b - q‖ := by
    calc ‖a - b‖ = ‖(a - p) + (p - q) - (b - q)‖ := by congr 1; abel
      _ ≤ ‖(a - p) + (p - q)‖ + ‖b - q‖ := norm_sub_le _ _
      _ ≤ ‖a - p‖ + ‖p - q‖ + ‖b - q‖ := by gcongr; exact norm_add_le _ _
  have h2 : 2 * rhoBar * δ / (α * (rhoBar - ρ))
      = rhoBar * δ / (α * (rhoBar - ρ)) + rhoBar * δ / (α * (rhoBar - ρ)) := by ring
  linarith

open MeasureTheory in
theorem part1_cov [FiniteDimensional ℝ E] {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) (Φ r : ExtFn E) (f : E → Ω → ℝ) (ρ rhoBar α δ thr : ℝ) (u0 : E)
    (hL : IsLegendre Φ) (hρ : ρ < rhoBar) (hrb : 0 ≤ rhoBar) (hα : 0 < α)
    (hu0 : u0 ∈ r.dom) (hu0i : u0 ∈ interior Φ.dom)
    (hsc : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom,
      α / 2 * ‖y - x‖ ^ 2 ≤ bregman Φ x y)
    (C : Set E) (T : Finset E)
    (hnet : ∀ y ∈ C, ∃ t ∈ T, ‖fderiv ℝ Φ.val y - fderiv ℝ Φ.val t‖ ≤ δ)
    (S : Fin m → Ω) (hwS : WeaklyConvexRel Φ (empRisk r f S) ρ)
    (hwP : WeaklyConvexRel Φ (popRisk P r f) ρ) (xS xb : E → E)
    (hxS : ∀ t ∈ T, xS t ∈ proxSet Φ (empRisk r f S) rhoBar t)
    (hxb : ∀ t ∈ T, xb t ∈ proxSet Φ (popRisk P r f) rhoBar t)
    (hS : ∃ y ∈ C, ∃ a ∈ proxSet Φ (empRisk r f S) rhoBar y,
      ∃ b ∈ proxSet Φ (popRisk P r f) rhoBar y,
        thr + 2 * rhoBar * δ / (α * (rhoBar - ρ)) < ‖a - b‖) :
    ∃ t ∈ T, thr < ‖xS t - xb t‖ := by
  obtain ⟨y, hy, a, ha, b, hb, hlt⟩ := hS
  obtain ⟨t, ht, hn⟩ := hnet y hy
  exact ⟨t, ht, cover_step Φ _ _ r.dom ρ rhoBar α δ thr u0 hL hwS hwP hρ hrb hα rfl rfl hu0 hu0i
    hsc y t a b _ _ ha hb (hxS t ht) (hxb t ht) hn hlt⟩

open MeasureTheory in
theorem good_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (G0 : Set Ω) (hG0 : P G0ᶜ = 0) :
    (Measure.pi fun _ : Fin m => P) {S | ∀ i, S i ∈ G0}ᶜ = 0 := by
  have h : {S : Fin m → Ω | ∀ i, S i ∈ G0}ᶜ = ⋃ i, Function.eval i ⁻¹' G0ᶜ := by
    ext S; simp
  rw [h]
  refine measure_iUnion_null fun i => ?_
  first
    | exact Measure.pi_eval_preimage_null _ hG0
    | exact Measure.pi_eval_preimage_null hG0
    | exact Measure.pi_eval_preimage_null (μ := fun _ : Fin m => P) hG0

theorem base_point [FiniteDimensional ℝ E] (Φ r : ExtFn E) (hcomp : Compatible Φ r)
    (hconv : Convex ℝ r.dom) (hne : r.dom.Nonempty) :
    ∃ u0 ∈ r.dom, u0 ∈ interior Φ.dom := by
  obtain ⟨u, hu⟩ := Set.Nonempty.intrinsicInterior hconv hne
  exact ⟨u, intrinsicInterior_subset hu, hcomp hu⟩

/-- Projection onto a good set: `proj G0 z0 z = z` on `G0`, `z0` off it. -/
noncomputable def projG {Ω : Type*} (G0 : Set Ω) (z0 : Ω) (z : Ω) : Ω := by
  classical exact if z ∈ G0 then z else z0

theorem projG_mem {Ω : Type*} (G0 : Set Ω) (z0 : Ω) (hz0 : z0 ∈ G0) (z : Ω) :
    projG G0 z0 z ∈ G0 := by
  classical
  unfold projG; split_ifs with h
  · exact h
  · exact hz0

theorem projG_of_mem {Ω : Type*} (G0 : Set Ω) (z0 z : Ω) (hz : z ∈ G0) :
    projG G0 z0 z = z := by
  classical
  unfold projG; simp [hz]

theorem projG_comp_update {Ω : Type*} {m : ℕ} (G0 : Set Ω) (z0 : Ω) (S : Fin m → Ω)
    (i : Fin m) (z : Ω) :
    projG G0 z0 ∘ Function.update S i z
      = Function.update (projG G0 z0 ∘ S) i (projG G0 z0 z) :=
  Function.comp_update _ _ _ _

theorem projG_measurable {Ω : Type*} [MeasurableSpace Ω] (G0 : Set Ω) (hG0 : MeasurableSet G0)
    (z0 : Ω) : Measurable (projG G0 z0) := by
  classical
  unfold projG
  exact Measurable.ite hG0 measurable_id measurable_const


/-! ## M_point (session 6): per-net-point hypotheses for point_tail_all / bias_bound. -/

/-- Replace-one stability at the Bregman level (the quantity used by `bias_bound`'s `Hstab`). -/
theorem replace_one_D {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m) (Φ r : ExtFn E)
    (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ rhoBar : ℝ) (hρ : ρ < rhoBar)
    (hsc0 : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom, 0 ≤ bregmanSym Φ x y)
    (hlip : ∀ x ∈ interior Φ.dom ∩ r.dom, ∀ y ∈ interior Φ.dom ∩ r.dom, ∀ z,
      |f x z - f y z| ≤ L z * Real.sqrt (bregmanSym Φ x y))
    (hL0 : ∀ z, 0 ≤ L z) (S : Fin m → Ω) (i : Fin m) (z : Ω) (t p₁ p₂ : E)
    (hw₁ : WeaklyConvexRel Φ (empRisk r f S) ρ)
    (hw₂ : WeaklyConvexRel Φ (empRisk r f (Function.update S i z)) ρ)
    (hp₁ : p₁ ∈ proxSet Φ (empRisk r f S) rhoBar t)
    (hp₂ : p₂ ∈ proxSet Φ (empRisk r f (Function.update S i z)) rhoBar t)
    (hi₁ : p₁ ∈ interior Φ.dom) (hi₂ : p₂ ∈ interior Φ.dom)
    (hdiff : DifferentiableOn ℝ Φ.val (interior Φ.dom)) :
    Real.sqrt (bregmanSym Φ p₁ p₂) ≤ (L (S i) + L z) / m / (rhoBar - ρ) := by
  have hr₁ : p₁ ∈ r.dom := hp₁.1.1
  have hr₂ : p₂ ∈ r.dom := hp₂.1.1
  have hd₁ : DifferentiableAt ℝ Φ.val p₁ :=
    (hdiff p₁ hi₁).differentiableAt (isOpen_interior.mem_nhds hi₁)
  have hd₂ : DifferentiableAt ℝ Φ.val p₂ :=
    (hdiff p₂ hi₂).differentiableAt (isOpen_interior.mem_nhds hi₂)
  have hst := prox_stability Φ (empRisk r f S) (empRisk r f (Function.update S i z)) ρ rhoBar t t
    p₁ p₂ rfl hw₁ hw₂ hp₁ hp₂ hd₁ hd₂
  simp only [sub_self, ContinuousLinearMap.zero_apply, mul_zero, add_zero] at hst
  rw [empRisk_update, empRisk_update] at hst
  have hsym : bregmanSym Φ p₂ p₁ = bregmanSym Φ p₁ p₂ := by unfold bregmanSym; ring
  have l1 := hlip p₂ ⟨hi₂, hr₂⟩ p₁ ⟨hi₁, hr₁⟩ (S i)
  have l2 := hlip p₁ ⟨hi₁, hr₁⟩ p₂ ⟨hi₂, hr₂⟩ z
  rw [hsym] at l1
  have hD0 : 0 ≤ bregmanSym Φ p₁ p₂ := hsc0 p₁ ⟨hr₁, hi₁⟩ p₂ ⟨hr₂, hi₂⟩
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hgap : 0 < rhoBar - ρ := sub_pos.mpr hρ
  have a1 := abs_le.mp l1
  have a2 := abs_le.mp l2
  have hq : (rhoBar - ρ) * bregmanSym Φ p₁ p₂
      ≤ ((L (S i) + L z) / m) * Real.sqrt (bregmanSym Φ p₁ p₂) := by
    have e : 1 / (m : ℝ) * (f p₂ (S i) - f p₂ z) - 1 / (m : ℝ) * (f p₁ (S i) - f p₁ z)
        = (1 / (m : ℝ)) * ((f p₂ (S i) - f p₁ (S i)) + (f p₁ z - f p₂ z)) := by ring
    rw [e] at hst
    calc _ ≤ _ := hst
      _ ≤ (1 / (m : ℝ)) * (L (S i) * Real.sqrt (bregmanSym Φ p₁ p₂)
            + L z * Real.sqrt (bregmanSym Φ p₁ p₂)) := by
          gcongr <;> linarith [a1.2, a2.2]
      _ = _ := by ring
  exact sqrt_le_of_quad _ _ _ hD0 hgap (div_nonneg (add_nonneg (hL0 _) (hL0 _)) hmR.le) hq

/-- `Hstab` of `bias_bound` for one good pair (S, z). -/
theorem stab_step {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m) (Φ r : ExtFn E)
    (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ rhoBar : ℝ) (hρ : ρ < rhoBar)
    (hsc0 : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom, 0 ≤ bregmanSym Φ x y)
    (hlip : ∀ x ∈ interior Φ.dom ∩ r.dom, ∀ y ∈ interior Φ.dom ∩ r.dom, ∀ z,
      |f x z - f y z| ≤ L z * Real.sqrt (bregmanSym Φ x y))
    (hL0 : ∀ z, 0 ≤ L z) (S : Fin m → Ω) (i : Fin m) (z : Ω) (t p₁ p₂ : E)
    (hw₁ : WeaklyConvexRel Φ (empRisk r f S) ρ)
    (hw₂ : WeaklyConvexRel Φ (empRisk r f (Function.update S i z)) ρ)
    (hp₁ : p₁ ∈ proxSet Φ (empRisk r f S) rhoBar t)
    (hp₂ : p₂ ∈ proxSet Φ (empRisk r f (Function.update S i z)) rhoBar t)
    (hi₁ : p₁ ∈ interior Φ.dom) (hi₂ : p₂ ∈ interior Φ.dom)
    (hdiff : DifferentiableOn ℝ Φ.val (interior Φ.dom)) :
    f p₂ (S i) - f p₁ (S i) ≤ L (S i) * (L (S i) + L z) / (m * (rhoBar - ρ)) := by
  have hs := replace_one_D hm Φ r f L ρ rhoBar hρ hsc0 hlip hL0 S i z t p₁ p₂ hw₁ hw₂ hp₁ hp₂
    hi₁ hi₂ hdiff
  have l1 := hlip p₂ ⟨hi₂, hp₂.1.1⟩ p₁ ⟨hi₁, hp₁.1.1⟩ (S i)
  have hsym : bregmanSym Φ p₂ p₁ = bregmanSym Φ p₁ p₂ := by unfold bregmanSym; ring
  rw [hsym] at l1
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hgap : 0 < rhoBar - ρ := sub_pos.mpr hρ
  have e : L (S i) * (L (S i) + L z) / (m * (rhoBar - ρ))
      = L (S i) * ((L (S i) + L z) / m / (rhoBar - ρ)) := by
    field_simp
  rw [e]
  calc f p₂ (S i) - f p₁ (S i) ≤ |f p₂ (S i) - f p₁ (S i)| := le_abs_self _
    _ ≤ L (S i) * Real.sqrt (bregmanSym Φ p₁ p₂) := l1
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (hL0 _)

/-- `H1` of `bias_bound` for one good sample. -/
theorem H1_step {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) {m : ℕ}
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (ρ rhoBar : ℝ)
    (hint : ∀ x, MeasureTheory.Integrable (f x) P) (S : Fin m → Ω) (t p xb : E)
    (hwS : WeaklyConvexRel Φ (empRisk r f S) ρ) (hwP : WeaklyConvexRel Φ (popRisk P r f) ρ)
    (hp : p ∈ proxSet Φ (empRisk r f S) rhoBar t) (hb : xb ∈ proxSet Φ (popRisk P r f) rhoBar t)
    (hdp : DifferentiableAt ℝ Φ.val p) (hdb : DifferentiableAt ℝ Φ.val xb) :
    (rhoBar - ρ) * bregmanSym Φ p xb
      ≤ (1 / (m : ℝ)) * ∑ i, (f xb (S i) - f p (S i)) - ∫ z, (f xb z - f p z) ∂P := by
  have hst := prox_stability Φ (empRisk r f S) (popRisk P r f) ρ rhoBar t t p xb rfl hwS hwP
    hp hb hdp hdb
  simp only [sub_self, ContinuousLinearMap.zero_apply, mul_zero, add_zero] at hst
  simp only [empRisk, popRisk] at hst
  rw [MeasureTheory.integral_sub (hint xb) (hint p), Finset.sum_sub_distrib]
  linarith [mul_sub (1 / (m : ℝ)) (∑ i, f xb (S i)) (∑ i, f p (S i))]

/-- Bounded differences of `S ↦ ‖x(proj ∘ S) - xb‖` with the projected loss bound `L ∘ proj`. -/
theorem point_hd [FiniteDimensional ℝ E] {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m)
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ rhoBar α : ℝ) (hα : 0 < α)
    (hρ : ρ < rhoBar) (hL : IsLegendre Φ)
    (hsc : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom,
      α / 2 * ‖y - x‖ ^ 2 ≤ bregman Φ x y)
    (hlip : ∀ x ∈ interior Φ.dom ∩ r.dom, ∀ y ∈ interior Φ.dom ∩ r.dom, ∀ z,
      |f x z - f y z| ≤ L z * Real.sqrt (bregmanSym Φ x y))
    (hL0 : ∀ z, 0 ≤ L z) (u0 : E) (hu0 : u0 ∈ r.dom) (hu0i : u0 ∈ interior Φ.dom)
    (G0 : Set Ω) (z0 : Ω) (hz0 : z0 ∈ G0)
    (hwS : ∀ S : Fin m → Ω, (∀ i, S i ∈ G0) → WeaklyConvexRel Φ (empRisk r f S) ρ)
    (t xb : E) (xsel : (Fin m → Ω) → E)
    (hsel : ∀ S, (∀ i, S i ∈ G0) → xsel S ∈ proxSet Φ (empRisk r f S) rhoBar t)
    (S : Fin m → Ω) (i : Fin m) (z : Ω) :
    |‖xsel (projG G0 z0 ∘ S) - xb‖ - ‖xsel (projG G0 z0 ∘ Function.update S i z) - xb‖|
      ≤ 1 / (Real.sqrt α * m * (rhoBar - ρ))
          * ((L ∘ projG G0 z0) (S i) + (L ∘ projG G0 z0) z) := by
  rw [projG_comp_update]
  have g1 : ∀ j, (projG G0 z0 ∘ S) j ∈ G0 := fun j => projG_mem G0 z0 hz0 _
  have g2 : ∀ j, Function.update (projG G0 z0 ∘ S) i (projG G0 z0 z) j ∈ G0 := by
    intro j
    rw [Function.update_apply]
    split_ifs
    · exact projG_mem G0 z0 hz0 _
    · exact g1 j
  have hp₁ := hsel _ g1
  have hp₂ := hsel _ g2
  have hi₁ := prox_interior Φ _ ρ rhoBar t _ u0 hL (hwS _ g1) hρ hp₁ hu0 hu0i
  have hi₂ := prox_interior Φ _ ρ rhoBar t _ u0 hL (hwS _ g2) hρ hp₂ hu0 hu0i
  have h := replace_one hm Φ r f L ρ rhoBar α hα hρ hsc hlip hL0 (projG G0 z0 ∘ S) i
    (projG G0 z0 z) t _ _ (hwS _ g1) (hwS _ g2) hp₁ hp₂ hi₁ hi₂ hL.differentiableOn
  calc _ ≤ ‖(xsel (projG G0 z0 ∘ S) - xb)
          - (xsel (Function.update (projG G0 z0 ∘ S) i (projG G0 z0 z)) - xb)‖ :=
        abs_norm_sub_norm_le _ _
    _ = ‖xsel (projG G0 z0 ∘ S)
          - xsel (Function.update (projG G0 z0 ∘ S) i (projG G0 z0 z))‖ := by
        rw [sub_sub_sub_cancel_right]
    _ ≤ _ := h

end S_M_point

section S_L_cover
set_option autoImplicit false

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## L_cover (session 6): net covering step, good-set nullity, interior base point. -/

end S_L_cover

section S_J_point
set_option autoImplicit false

open MeasureTheory Real Filter

theorem cosh_add_le (u v : ℝ) : cosh (u + v) ≤ (cosh (2 * u) + cosh (2 * v)) / 2 := by
  rw [Real.cosh_add, Real.cosh_two_mul, Real.cosh_two_mul]
  nlinarith [sq_nonneg (cosh u - cosh v), sq_nonneg (sinh u - sinh v)]

theorem integrable_of_abs_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)

theorem integrable_exp_of_abs_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    Integrable (fun x => exp (f x)) μ :=
  integrable_of_abs_le hf.exp (exp M) fun x => by
    rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.2 ((le_abs_self _).trans (hM x))

theorem abs_integral_le_of_abs_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (C : ℝ) (h : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le (integrable_const (μ := μ) C)
    (Eventually.of_forall fun x => (by simpa [Real.norm_eq_abs] using h x : ‖f x‖ ≤ C))
  simpa [Real.norm_eq_abs] using this

theorem abs_mul_sub_le (l x E M : ℝ) (hx : |x| ≤ M) : |l * (x - E)| ≤ |l| * (M + |E|) := by
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 := abs_le.1 hx
  exact abs_le.2 ⟨by linarith [neg_abs_le E, le_abs_self E], by linarith [neg_abs_le E, le_abs_self E]⟩

/-- One coordinate: Jensen (`exp x ≥ 1 + x`) plus symmetrization with `cosh`. -/
theorem sym_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (c l : ℝ) (hint : Integrable (fun z => cosh (2 * l * c * L z)) P)
    (h : Ω → ℝ) (hm : Measurable h) (M : ℝ) (hM : ∀ a, |h a| ≤ M)
    (hd : ∀ a b, |h a - h b| ≤ c * (L a + L b)) :
    ∫ a, exp (l * (h a - ∫ b, h b ∂P)) ∂P ≤ ∫ z, cosh (2 * l * c * L z) ∂P := by
  set I := ∫ b, h b ∂P
  set K := ∫ z, cosh (2 * l * c * L z) ∂P
  have hlh : ∀ a, |l * h a| ≤ |l| * M := fun a => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM a) (abs_nonneg _)
  have hih : Integrable h P := integrable_of_abs_le hm M hM
  have iA : Integrable (fun a => exp (l * h a)) P :=
    integrable_exp_of_abs_le (hm.const_mul l) _ hlh
  have iB : Integrable (fun a => exp (-l * h a)) P :=
    integrable_exp_of_abs_le (hm.const_mul (-l)) (|l| * M) fun a => by
      rw [neg_mul, abs_neg]; exact hlh a
  set A := ∫ a, exp (l * h a) ∂P
  set B := ∫ a, exp (-l * h a) ∂P
  have hA0 : 0 ≤ A := integral_nonneg fun a => (exp_pos _).le
  -- step 1
  have h1 : ∫ a, exp (l * (h a - I)) ∂P = exp (-l * I) * A := by
    rw [← integral_const_mul]; congr 1; ext a; rw [← exp_add]; ring_nf
  -- step 2: exp(-l I) ≤ B
  have h2 : exp (-l * I) ≤ B := by
    have hpt : ∀ b, exp (-l * I) * (1 + -l * (h b - I)) ≤ exp (-l * h b) := fun b => by
      have := add_one_le_exp (-l * (h b - I))
      calc exp (-l * I) * (1 + -l * (h b - I)) ≤ exp (-l * I) * exp (-l * (h b - I)) :=
            mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
        _ = exp (-l * h b) := by rw [← exp_add]; ring_nf
    have hsub' : Integrable (fun b => -l * (h b - I)) P := (hih.sub (integrable_const I)).const_mul (-l)
    have hint2 : Integrable (fun b => exp (-l * I) * (1 + -l * (h b - I))) P :=
      ((integrable_const 1).add hsub').const_mul _
    have hle := integral_mono hint2 iB hpt
    have hcomp : ∫ b, exp (-l * I) * (1 + -l * (h b - I)) ∂P = exp (-l * I) := by
      rw [integral_const_mul, integral_add (integrable_const _) hsub', integral_const_mul,
        integral_sub hih (integrable_const I)]
      simp [I]
    linarith
  -- step 3: A * B ≤ K
  have h3 : A * B ≤ K := by
    have hpt : ∀ a, exp (l * h a) * B / 2 + exp (-l * h a) * A / 2
        ≤ (cosh (2 * l * c * L a) + K) / 2 := by
      intro a
      have heq : exp (l * h a) * B / 2 + exp (-l * h a) * A / 2
          = ∫ b, cosh (l * (h a - h b)) ∂P := by
        have hc : ∀ b, cosh (l * (h a - h b))
            = exp (l * h a) * exp (-l * h b) / 2 + exp (-l * h a) * exp (l * h b) / 2 := by
          intro b; rw [Real.cosh_eq, ← exp_add, ← exp_add]; ring_nf
        simp_rw [hc]
        rw [integral_add ((iB.const_mul _).div_const _) ((iA.const_mul _).div_const _),
          integral_div, integral_div, integral_const_mul, integral_const_mul]
      rw [heq]
      have hcI : Integrable (fun b => cosh (l * (h a - h b))) P := by
        refine integrable_of_abs_le (by fun_prop) (cosh (2 * |l| * M)) fun b => ?_
        rw [abs_of_pos (cosh_pos _)]
        refine Real.cosh_le_cosh.2 (le_trans ?_ (le_abs_self _))
        rw [abs_mul]
        have hab : |h a - h b| ≤ 2 * M := by
          have h1 := abs_le.1 (hM a); have h2 := abs_le.1 (hM b)
          exact abs_le.2 ⟨by linarith, by linarith⟩
        nlinarith [abs_nonneg l]
      have hpt2 : ∀ b, cosh (l * (h a - h b))
          ≤ (cosh (2 * l * c * L a) + cosh (2 * l * c * L b)) / 2 := by
        intro b
        calc cosh (l * (h a - h b)) ≤ cosh (l * c * L a + l * c * L b) := by
              refine Real.cosh_le_cosh.2 ?_
              rw [abs_mul, show l * c * L a + l * c * L b = l * (c * (L a + L b)) by ring, abs_mul]
              exact mul_le_mul_of_nonneg_left ((hd a b).trans (le_abs_self _)) (abs_nonneg _)
          _ ≤ _ := by
              have := cosh_add_le (l * c * L a) (l * c * L b)
              simpa [mul_assoc] using this
      have hR : Integrable (fun b => (cosh (2 * l * c * L a) + cosh (2 * l * c * L b)) / 2) P :=
        ((integrable_const _).add hint).div_const _
      calc ∫ b, cosh (l * (h a - h b)) ∂P
          ≤ ∫ b, (cosh (2 * l * c * L a) + cosh (2 * l * c * L b)) / 2 ∂P :=
            integral_mono hcI hR hpt2
        _ = (cosh (2 * l * c * L a) + K) / 2 := by
            rw [integral_div, integral_add (integrable_const _) hint]; simp [K]
    have hL : Integrable (fun a => exp (l * h a) * B / 2 + exp (-l * h a) * A / 2) P :=
      (iA.mul_const _ |>.div_const _).add (iB.mul_const _ |>.div_const _)
    have hRi : Integrable (fun a => (cosh (2 * l * c * L a) + K) / 2) P :=
      (hint.add (integrable_const _)).div_const _
    have hle := integral_mono hL hRi hpt
    rw [integral_add ((iA.mul_const _).div_const _) ((iB.mul_const _).div_const _),
      integral_div, integral_div, integral_mul_const, integral_mul_const, integral_div,
      integral_add hint (integrable_const _)] at hle
    simp only [integral_const, probReal_univ, one_smul] at hle
    change A * B / 2 + B * A / 2 ≤ (K + K) / 2 at hle
    nlinarith
  rw [h1]
  calc exp (-l * I) * A ≤ B * A := mul_le_mul_of_nonneg_right h2 hA0
    _ = A * B := mul_comm _ _
    _ ≤ K := h3

/-- D7 core: exponential moment of the centred bounded-difference function on `Measure.pi`. -/
theorem bdd_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (c l : ℝ) (hint : Integrable (fun z => cosh (2 * l * c * L z)) P) :
    ∀ (m : ℕ) (g : (Fin m → Ω) → ℝ), Measurable g → ∀ M : ℝ, (∀ S, |g S| ≤ M) →
      (∀ S i z, |g S - g (Function.update S i z)| ≤ c * (L (S i) + L z)) →
      ∫ S, exp (l * (g S - ∫ T, g T ∂(Measure.pi fun _ : Fin m => P)))
          ∂(Measure.pi fun _ : Fin m => P)
        ≤ (∫ z, cosh (2 * l * c * L z) ∂P) ^ m := by
  have hK0 : 0 ≤ ∫ z, cosh (2 * l * c * L z) ∂P := integral_nonneg fun z => (cosh_pos _).le
  intro m
  induction m with
  | zero =>
    intro g _ M _ _
    have hc : ∀ S : Fin 0 → Ω, g S - ∫ T, g T ∂(Measure.pi fun _ : Fin 0 => P) = 0 := by
      intro S
      have : (fun T : Fin 0 → Ω => g T) = fun _ => g S :=
        funext fun T => by rw [Subsingleton.elim T S]
      rw [this, integral_const]; simp
    simp [hc]
  | succ n ih =>
    intro g hg M hM hd
    set ν := Measure.pi fun _ : Fin n => P with hν
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) 0 with he_def
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n+1) => P) (P.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => P) 0
    have he : ∀ p : Ω × (Fin n → Ω), e.symm p = Fin.cons p.1 p.2 := by
      intro p; simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; simp [Fin.insertNthEquiv_zero]
      rfl
    have htr : ∀ F : (Fin (n+1) → Ω) → ℝ,
        ∫ S, F S ∂(Measure.pi fun _ : Fin (n+1) => P)
          = ∫ p, F (Fin.cons p.1 p.2) ∂(P.prod ν) := by
      intro F
      have := hmp.integral_comp' (fun p => F (e.symm p))
      simp only [MeasurableEquiv.symm_apply_apply] at this
      rw [this]; simp_rw [he]
    set G : Ω × (Fin n → Ω) → ℝ := fun p => g (Fin.cons p.1 p.2) with hGdef
    have hGm : Measurable G := by
      rw [show G = g ∘ e.symm from funext fun p => by rw [Function.comp_apply, he]]
      exact hg.comp e.symm.measurable
    have hGb : ∀ p, |G p| ≤ M := fun p => hM _
    have hGint : Integrable G (P.prod ν) := integrable_of_abs_le hGm M hGb
    set h : Ω → ℝ := fun a => ∫ R, G (a, R) ∂ν with hdef
    have hh : Measurable h := (hGm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have hGa : ∀ a, Integrable (fun R => G (a, R)) ν := fun a =>
      integrable_of_abs_le (hGm.comp measurable_prodMk_left) M fun R => hGb (a, R)
    have hhb : ∀ a, |h a| ≤ M := fun a => abs_integral_le_of_abs_le M fun R => hGb (a, R)
    have hhd : ∀ a b, |h a - h b| ≤ c * (L a + L b) := by
      intro a b
      rw [hdef, ← integral_sub (hGa a) (hGa b)]
      refine abs_integral_le_of_abs_le _ fun R => ?_
      have := hd (Fin.cons a R) 0 b
      rwa [Fin.update_cons_zero, Fin.cons_zero] at this
    have hE : ∫ S, g S ∂(Measure.pi fun _ : Fin (n+1) => P) = ∫ a, h a ∂P := by
      rw [htr g]; exact integral_prod G hGint
    rw [hE, htr (fun S => exp (l * (g S - ∫ a, h a ∂P)))]
    set Ih := ∫ a, h a ∂P with hIh
    have hF : Integrable (fun p => exp (l * (G p - Ih))) (P.prod ν) :=
      integrable_exp_of_abs_le ((hGm.sub_const _).const_mul l) _
        fun p => abs_mul_sub_le l _ _ M (hGb p)
    change ∫ p, exp (l * (G p - Ih)) ∂(P.prod ν) ≤ _
    rw [integral_prod _ hF]
    have hpt : ∀ a, ∫ R, exp (l * (G (a, R) - Ih)) ∂ν
        ≤ exp (l * (h a - Ih)) * (∫ z, cosh (2 * l * c * L z) ∂P) ^ n := by
      intro a
      have hsplit : ∫ R, exp (l * (G (a, R) - Ih)) ∂ν
          = exp (l * (h a - Ih)) * ∫ R, exp (l * (G (a, R) - h a)) ∂ν := by
        rw [← integral_const_mul]; congr 1; ext R; rw [← exp_add]; ring_nf
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
      refine ih (fun R => G (a, R)) (hGm.comp measurable_prodMk_left) M (fun R => hGb (a, R)) ?_
      intro R j z
      have := hd (Fin.cons a R) j.succ z
      rwa [Fin.cons_succ, ← Fin.cons_update] at this
    have hRi : Integrable (fun a => exp (l * (h a - Ih)) * (∫ z, cosh (2 * l * c * L z) ∂P) ^ n) P :=
      (integrable_exp_of_abs_le ((hh.sub_const _).const_mul l) _
        fun a => abs_mul_sub_le l _ _ M (hhb a)).mul_const _
    calc ∫ a, ∫ R, exp (l * (G (a, R) - Ih)) ∂ν ∂P
        ≤ ∫ a, exp (l * (h a - Ih)) * (∫ z, cosh (2 * l * c * L z) ∂P) ^ n ∂P :=
          integral_mono hF.integral_prod_left hRi hpt
      _ = (∫ a, exp (l * (h a - Ih)) ∂P) * (∫ z, cosh (2 * l * c * L z) ∂P) ^ n :=
          integral_mul_const _ _
      _ ≤ (∫ z, cosh (2 * l * c * L z) ∂P) * (∫ z, cosh (2 * l * c * L z) ∂P) ^ n :=
          mul_le_mul_of_nonneg_right (sym_step P L c l hint h hh M hhb hhd) (pow_nonneg hK0 n)
      _ = (∫ z, cosh (2 * l * c * L z) ∂P) ^ (n + 1) := by ring

/-- D7: Chernoff tail for a bounded, measurable, bounded-difference function of `m` iid samples. -/
theorem bdd_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (c l : ℝ) (hl : 0 ≤ l) (hint : Integrable (fun z => cosh (2 * l * c * L z)) P)
    (m : ℕ) (g : (Fin m → Ω) → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ S, |g S| ≤ M)
    (hd : ∀ S i z, |g S - g (Function.update S i z)| ≤ c * (L (S i) + L z)) (u : ℝ) :
    (Measure.pi fun _ : Fin m => P).real
        {S | u ≤ g S - ∫ T, g T ∂(Measure.pi fun _ : Fin m => P)}
      ≤ exp (-l * u) * (∫ z, cosh (2 * l * c * L z) ∂P) ^ m := by
  refine (ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := fun S => g S - ∫ T, g T ∂(Measure.pi fun _ : Fin m => P)) u hl
    (integrable_exp_of_abs_le ((hg.sub_const _).const_mul l) _
      fun S => abs_mul_sub_le l _ _ M (hM S))).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
  unfold ProbabilityTheory.mgf
  exact bdd_mgf P L c l hint m g hg M hM hd

/-- D6 tool: replacing coordinate `i` by a fresh sample and keeping the old one is measure
preserving on `(pi P) × P` (exchangeability used in the swap argument for the bias bound). -/
theorem swap_mp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → Ω) × Ω => (Function.update p.1 i p.2, p.1 i))
      ((Measure.pi fun _ : Fin m => P).prod P) ((Measure.pi fun _ : Fin m => P).prod P) := by
  cases m with
  | zero => exact i.elim0
  | succ n =>
    set ν := Measure.pi fun _ : Fin n => P
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) i
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n+1) => P) (P.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => P) i
    have h2 : MeasurePreserving (Prod.map e id)
        ((Measure.pi fun _ : Fin (n+1) => P).prod P) ((P.prod ν).prod P) :=
      hmp.prod (MeasurePreserving.id P)
    have h2s : MeasurePreserving (Prod.map e.symm id)
        ((P.prod ν).prod P) ((Measure.pi fun _ : Fin (n+1) => P).prod P) :=
      hmp.symm.prod (MeasurePreserving.id P)
    have hσ : MeasurePreserving (fun q : (Ω × (Fin n → Ω)) × Ω => ((q.2, q.1.2), q.1.1))
        ((P.prod ν).prod P) ((P.prod ν).prod P) := by
      have a1 := measurePreserving_prodAssoc P ν P
      have a2 : MeasurePreserving
          (Prod.map (id : Ω → Ω) (Prod.swap : (Fin n → Ω) × Ω → Ω × (Fin n → Ω)))
          (P.prod (ν.prod P)) (P.prod (P.prod ν)) :=
        (MeasurePreserving.id P).prod Measure.measurePreserving_swap
      have a3 : MeasurePreserving (Prod.swap : Ω × (Ω × (Fin n → Ω)) → _)
          (P.prod (P.prod ν)) ((P.prod ν).prod P) := Measure.measurePreserving_swap
      convert a3.comp (a2.comp a1) using 1
      funext q; rfl
    have hall := h2s.comp (hσ.comp h2)
    convert hall using 1
    funext p
    refine Prod.ext ?_ rfl
    simp [e, Fin.insertNthEquiv]

/-- D7 in the target's shape: per-net-point tail `exp(-m(λ s/√m - log E cosh(λL)))`. -/
theorem tail_shape {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (c lam s : ℝ) (hc : 0 < c) (hlam : 0 ≤ lam)
    (hint : Integrable (fun z => cosh (lam * L z)) P)
    (m : ℕ) (hm : 0 < m) (g : (Fin m → Ω) → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ S, |g S| ≤ M)
    (hd : ∀ S i z, |g S - g (Function.update S i z)| ≤ c * (L (S i) + L z)) (thr : ℝ)
    (hthr : ∫ T, g T ∂(Measure.pi fun _ : Fin m => P) + 2 * c * s * Real.sqrt m ≤ thr) :
    (Measure.pi fun _ : Fin m => P) {S | thr < g S}
      ≤ ENNReal.ofReal (exp (-((m : ℝ) * (lam * (s / Real.sqrt m)
          - Real.log (∫ z, cosh (lam * L z) ∂P))))) := by
  set l := lam / (2 * c) with hl
  have hl0 : 0 ≤ l := div_nonneg hlam (by linarith)
  have hlc : 2 * l * c = lam := by rw [hl]; field_simp
  have hint' : Integrable (fun z => cosh (2 * l * c * L z)) P := by simpa [hlc] using hint
  set u := 2 * c * s * Real.sqrt m
  have ht := bdd_tail P L c l hl0 hint' m g hg M hM hd u
  rw [hlc] at ht
  set K := ∫ z, cosh (lam * L z) ∂P
  have hK1 : 1 ≤ K := by
    have : ∫ _z, (1 : ℝ) ∂P ≤ K := integral_mono (integrable_const 1) hint fun z => one_le_cosh _
    simpa using this
  have hsub : {S | thr < g S} ⊆
      {S | u ≤ g S - ∫ T, g T ∂(Measure.pi fun _ : Fin m => P)} := by
    intro S hS; change thr < g S at hS; change u ≤ _; linarith
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (ht.trans (le_of_eq ?_))
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hKm : K ^ m = exp (m * Real.log K) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  rw [hKm, ← exp_add]
  congr 1
  have h1 : l * u = lam * s * Real.sqrt m := by
    simp only [u, hl]
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring
  have h2 : (m : ℝ) * (lam * (s / Real.sqrt m)) = lam * s * Real.sqrt m := by
    rw [show (m : ℝ) * (lam * (s / Real.sqrt m))
        = Real.sqrt m * Real.sqrt m * (lam * (s / Real.sqrt m)) by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg m)]]
    rw [show Real.sqrt m * Real.sqrt m * (lam * (s / Real.sqrt m))
        = lam * s * Real.sqrt m * (Real.sqrt m / Real.sqrt m) by ring, div_self hsm.ne', mul_one]
  rw [neg_mul, h1, mul_sub, h2]; ring

theorem trunc_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (G D : X → ℝ) (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x) (hDi : Integrable D μ)
    (α : ℝ) (hα : 0 < α) (hGD : ∀ x, α * G x ^ 2 ≤ D x) (M : ℝ) (hM : 0 ≤ M)
    (B : ℝ) (hB : ∫ x, D x ∂μ ≤ B) :
    ∫ x, min (G x) M ∂μ ≤ Real.sqrt (B / α) := by
  set h : X → ℝ := fun x => min (G x) M with hh
  have hm : Measurable h := hG.min measurable_const
  have h0 : ∀ x, 0 ≤ h x := fun x => le_min (hG0 x) hM
  have hle : ∀ x, h x ≤ M := fun x => min_le_right _ _
  have hbd : ∀ᵐ x ∂μ, ‖h x‖ ≤ M := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hle x
  have hmem : MemLp h 2 μ := MemLp.of_bound hm.aestronglyMeasurable M hbd
  have hsqI : Integrable (fun x => h x ^ 2) μ := hmem.integrable_sq
  have hvar := ProbabilityTheory.variance_eq_sub hmem
  have hvn := ProbabilityTheory.variance_nonneg h μ
  have hj : (∫ x, h x ∂μ) ^ 2 ≤ ∫ x, h x ^ 2 ∂μ := by
    have : (∫ x, (h ^ 2) x ∂μ) - (∫ x, h x ∂μ) ^ 2 ≥ 0 := by rw [← hvar]; exact hvn
    simpa [Pi.pow_apply] using this
  have h2 : ∫ x, h x ^ 2 ∂μ ≤ ∫ x, D x / α ∂μ := by
    refine integral_mono hsqI (hDi.div_const α) fun x => ?_
    have e1 : h x ^ 2 ≤ G x ^ 2 := pow_le_pow_left₀ (h0 x) (min_le_left _ _) 2
    have e2 : G x ^ 2 ≤ D x / α := by rw [le_div_iff₀ hα]; linarith [hGD x]
    exact e1.trans e2
  have h3 : ∫ x, D x / α ∂μ ≤ B / α := by
    rw [integral_div]; exact div_le_div_of_nonneg_right hB hα.le
  exact (le_abs_self _).trans (Real.abs_le_sqrt (hj.trans (h2.trans h3)))


/-- Per-net-point tail: bounded differences + second-moment bound give the target RHS. -/
theorem point_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (σ s lam α gap : ℝ) (hσ : Real.sqrt (∫ z, L z ^ 2 ∂P) ≤ σ)
    (hs : 0 ≤ s) (hlam : 0 ≤ lam) (hint : Integrable (fun z => cosh (lam * L z)) P)
    (hα : 0 < α) (hgap : 0 < gap) (m : ℕ) (hm : 0 < m)
    (G : (Fin m → Ω) → ℝ) (hG : Measurable G) (hG0 : ∀ S, 0 ≤ G S)
    (hd : ∀ S i z, |G S - G (Function.update S i z)|
      ≤ 1 / (Real.sqrt α * m * gap) * (L (S i) + L z))
    (hDi : Integrable (fun S => α * G S ^ 2) (Measure.pi fun _ : Fin m => P))
    (hEB : ∫ S, α * G S ^ 2 ∂(Measure.pi fun _ : Fin m => P)
      ≤ 2 * (∫ z, L z ^ 2 ∂P) / (m * gap ^ 2)) :
    (Measure.pi fun _ : Fin m => P) {S | Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) < G S}
      ≤ ENNReal.ofReal (exp (-((m : ℝ) * (lam * (s / Real.sqrt m)
          - Real.log (∫ z, cosh (lam * L z) ∂P))))) := by
  have hI0 : 0 ≤ ∫ z, L z ^ 2 ∂P := integral_nonneg fun z => sq_nonneg _
  have hσ0 : 0 ≤ σ := (Real.sqrt_nonneg _).trans hσ
  have hI : ∫ z, L z ^ 2 ∂P ≤ σ ^ 2 := by
    have := Real.sq_sqrt hI0
    nlinarith [Real.sqrt_nonneg (∫ z, L z ^ 2 ∂P)]
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hsa : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  obtain ⟨K, hK⟩ : ∃ K, K = Real.sqrt α * gap * Real.sqrt m := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hK2 : K ^ 2 = α * gap ^ 2 * m := by
    rw [hK, mul_pow, mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt hmR.le]
  have hthr : Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) = 2 * (σ + s) / K := by
    rw [← hK2, show 4 * (σ + s) ^ 2 = (2 * (σ + s)) ^ 2 by ring, ← div_pow,
      Real.sqrt_sq (by positivity)]
  have hM0 : 0 ≤ Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1 := by positivity
  have hc : 0 < 1 / (Real.sqrt α * m * gap) := by positivity
  have hdg : ∀ S i z, |min (G S) (Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1)
      - min (G (Function.update S i z)) (Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1)|
      ≤ 1 / (Real.sqrt α * m * gap) * (L (S i) + L z) := by
    intro S i z
    refine le_trans ?_ (hd S i z)
    have := abs_min_sub_min_le_max (G S) (Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1)
      (G (Function.update S i z)) (Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1)
    simpa using this
  have hgM : ∀ S, |min (G S) (Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1)|
      ≤ Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1 := fun S => by
    rw [abs_of_nonneg (le_min (hG0 S) hM0)]; exact min_le_right _ _
  have hEg := trunc_mean_le (Measure.pi fun _ : Fin m => P) G (fun S => α * G S ^ 2) hG hG0 hDi
    α hα (fun S => le_rfl) _ hM0 _ hEB
  have hsq : Real.sqrt ((2 * (∫ z, L z ^ 2 ∂P) / (m * gap ^ 2)) / α) ≤ 2 * σ / K := by
    calc Real.sqrt ((2 * (∫ z, L z ^ 2 ∂P) / (m * gap ^ 2)) / α)
        ≤ Real.sqrt ((2 * σ / K) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, hK2,
            show (2 * (∫ z, L z ^ 2 ∂P) / (m * gap ^ 2)) / α
              = 2 * (∫ z, L z ^ 2 ∂P) / (α * gap ^ 2 * m) by field_simp]
          gcongr
          nlinarith
      _ = 2 * σ / K := Real.sqrt_sq (by positivity)
  have hcK : 1 / (Real.sqrt α * m * gap) * Real.sqrt m = 1 / K := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) hKpos.ne', hK]
    have h2 : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmR.le
    linear_combination (Real.sqrt α * gap) * h2
  have hthr0 : ∫ S, min (G S) (Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1)
        ∂(Measure.pi fun _ : Fin m => P)
      + 2 * (1 / (Real.sqrt α * m * gap)) * s * Real.sqrt m
      ≤ Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) := by
    rw [show 2 * (1 / (Real.sqrt α * m * gap)) * s * Real.sqrt m
      = 2 * s * (1 / (Real.sqrt α * m * gap) * Real.sqrt m) by ring, hcK]
    have : 2 * (σ + s) / K = 2 * σ / K + 2 * s * (1 / K) := by ring
    linarith [hthr, hEg, hsq]
  refine le_trans (measure_mono ?_) (tail_shape P L _ lam s hc hlam hint m hm
    (fun S => min (G S) (Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) + 1))
    (hG.min measurable_const) _ hgM hdg _ hthr0)
  intro S hS
  simp only [Set.mem_setOf_eq] at hS ⊢
  exact lt_min hS (lt_add_one _)


theorem rhs_ge_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (lam s : ℝ) (hlam : lam ≤ 0) (hs : 0 ≤ s)
    (hint : Integrable (fun z => cosh (lam * L z)) P) (m : ℕ) :
    1 ≤ ENNReal.ofReal (exp (-((m : ℝ) * (lam * (s / Real.sqrt m)
          - Real.log (∫ z, cosh (lam * L z) ∂P))))) := by
  have h1 : 1 ≤ ∫ z, cosh (lam * L z) ∂P := by
    calc (1:ℝ) = ∫ z, (1:ℝ) ∂P := by simp
      _ ≤ _ := integral_mono (integrable_const 1) hint (fun z => Real.one_le_cosh _)
  have hlog : 0 ≤ Real.log (∫ z, cosh (lam * L z) ∂P) := Real.log_nonneg h1
  have hls : lam * (s / Real.sqrt m) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hlam (by positivity)
  have h0 : 0 ≤ -((m : ℝ) * (lam * (s / Real.sqrt m) - Real.log (∫ z, cosh (lam * L z) ∂P))) := by
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp h0)

/-- `point_tail` for every `lam` (for `lam < 0` the right side is at least one). -/
theorem point_tail_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Ω → ℝ) (σ s lam α gap : ℝ) (hσ : Real.sqrt (∫ z, L z ^ 2 ∂P) ≤ σ)
    (hs : 0 ≤ s) (hint : Integrable (fun z => cosh (lam * L z)) P)
    (hα : 0 < α) (hgap : 0 < gap) (m : ℕ) (hm : 0 < m)
    (G : (Fin m → Ω) → ℝ) (hG : Measurable G) (hG0 : ∀ S, 0 ≤ G S)
    (hd : ∀ S i z, |G S - G (Function.update S i z)|
      ≤ 1 / (Real.sqrt α * m * gap) * (L (S i) + L z))
    (hDi : Integrable (fun S => α * G S ^ 2) (Measure.pi fun _ : Fin m => P))
    (hEB : ∫ S, α * G S ^ 2 ∂(Measure.pi fun _ : Fin m => P)
      ≤ 2 * (∫ z, L z ^ 2 ∂P) / (m * gap ^ 2)) :
    (Measure.pi fun _ : Fin m => P) {S | Real.sqrt (4 * (σ + s) ^ 2 / (α * gap ^ 2 * m)) < G S}
      ≤ ENNReal.ofReal (exp (-((m : ℝ) * (lam * (s / Real.sqrt m)
          - Real.log (∫ z, cosh (lam * L z) ∂P))))) := by
  by_cases hl : 0 ≤ lam
  · exact point_tail P L σ s lam α gap hσ hs hl hint hα hgap m hm G hG hG0 hd hDi hEB
  · exact le_trans prob_le_one (rhs_ge_one P L lam s (not_le.mp hl).le hs hint m)

/-- Union bound over the net, with an exceptional null set. -/
theorem union_net {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (Ev Good : Set X)
    (hGood : μ Goodᶜ = 0) (T : Finset ι) (G : ι → X → ℝ) (thr : ℝ) (R : ENNReal)
    (hR : ∀ t ∈ T, μ {S | thr < G t S} ≤ R)
    (hcov : ∀ S ∈ Good, S ∈ Ev → ∃ t ∈ T, thr < G t S) :
    μ Ev ≤ (T.card : ENNReal) * R := by
  calc μ Ev ≤ μ (Goodᶜ ∪ ⋃ t ∈ T, {S | thr < G t S}) := by
        apply measure_mono
        intro S hS
        by_cases hg : S ∈ Good
        · right
          obtain ⟨t, ht, h⟩ := hcov S hg hS
          exact Set.mem_biUnion ht h
        · left; exact hg
    _ ≤ μ Goodᶜ + μ (⋃ t ∈ T, {S | thr < G t S}) := measure_union_le _ _
    _ ≤ 0 + ∑ t ∈ T, μ {S | thr < G t S} := by
        rw [hGood]; gcongr; exact measure_biUnion_finset_le _ _
    _ ≤ (T.card : ENNReal) * R := by
        rw [zero_add]
        calc ∑ t ∈ T, μ {S | thr < G t S} ≤ ∑ _t ∈ T, R := Finset.sum_le_sum hR
          _ = (T.card : ENNReal) * R := by rw [Finset.sum_const, nsmul_eq_mul]

end S_J_point

section S_F_bias
set_option autoImplicit false

open MeasureTheory Real

theorem integrable_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → ℝ} (hg : Integrable g ν) : Integrable (fun x => g (f x)) μ := by
  have h := hg
  rw [← hf.map_eq] at h
  exact h.comp_measurable hf.measurable

theorem integral_comp_mp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    {g : β → ℝ} (hg : AEStronglyMeasurable g ν) : ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hf.map_eq] at hg ⊢
  exact (integral_map hf.measurable.aemeasurable hg).symm

theorem bias_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (L : Ω → ℝ) (hL0 : ∀ z, 0 ≤ L z) (hL2 : MemLp L 2 P)
    (a : Ω → ℝ) (ha : Measurable a)
    (F : (Fin m → Ω) → Ω → ℝ) (hF : Measurable (Function.uncurry F))
    (D : (Fin m → Ω) → ℝ) (hD0 : ∀ S, 0 ≤ D S)
    (D₂ : (Fin m → Ω) → ℝ) (hD2m : AEStronglyMeasurable D₂ (Measure.pi fun _ : Fin m => P))
    (hD20 : ∀ S, 0 ≤ D₂ S) (hD2le : ∀ S, D₂ S ≤ D S) (gap : ℝ) (hgap : 0 < gap)
    (hlip : ∀ S z, |a z - F S z| ≤ L z * Real.sqrt (D S))
    (H1 : ∀ᵐ S ∂(Measure.pi fun _ : Fin m => P),
      gap * D S ≤ (1 / (m : ℝ)) * ∑ i, (a (S i) - F S (S i)) - ∫ z, (a z - F S z) ∂P)
    (Hstab : ∀ i : Fin m, ∀ᵐ p ∂((Measure.pi fun _ : Fin m => P).prod P),
      F (Function.update p.1 i p.2) (p.1 i) - F p.1 (p.1 i)
        ≤ L (p.1 i) * (L (p.1 i) + L p.2) / (m * gap)) :
    Integrable D₂ (Measure.pi fun _ : Fin m => P) ∧
    gap * ∫ S, D₂ S ∂(Measure.pi fun _ : Fin m => P) ≤ 2 * (∫ z, L z ^ 2 ∂P) / (m * gap) := by
  set Q := Measure.pi fun _ : Fin m => P with hQ
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL1 : Integrable L P := hL2.integrable one_le_two
  have hLL : Integrable (fun z => L z ^ 2) P := hL2.integrable_sq
  have hLLnn : 0 ≤ ∫ z, L z ^ 2 ∂P := integral_nonneg fun z => sq_nonneg _
  set c := ∫ z, L z ∂P with hc
  have hc0 : 0 ≤ c := integral_nonneg hL0
  set A : (Fin m → Ω) → ℝ := fun S => (1 / (m : ℝ)) * ∑ i, L (S i) + c with hA
  have hA0 : ∀ S, 0 ≤ A S := fun S =>
    add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hL0 _)) hc0
  have hevi : ∀ i : Fin m, MeasurePreserving (fun S : Fin m → Ω => S i) Q P :=
    fun i => measurePreserving_eval (μ := fun _ : Fin m => P) i
  have hAm : MemLp A 2 Q := by
    have hs : MemLp (fun S : Fin m → Ω => ∑ i, L (S i)) 2 Q :=
      memLp_finsetSum _ fun i _ => hL2.comp_measurePreserving (hevi i)
    exact (hs.const_mul (1 / (m : ℝ))).add (memLp_const c)
  have hA2 : Integrable (fun S => A S ^ 2) Q := hAm.integrable_sq
  have hfst : MeasurePreserving (Prod.fst : (Fin m → Ω) × Ω → _) (Q.prod P) Q :=
    measurePreserving_fst (μ := Q) (ν := P)
  have hsnd : MeasurePreserving (Prod.snd : (Fin m → Ω) × Ω → _) (Q.prod P) P :=
    measurePreserving_snd (μ := Q) (ν := P)
  have hpi : ∀ i : Fin m, MeasurePreserving (fun p : (Fin m → Ω) × Ω => p.1 i) (Q.prod P) P :=
    fun i => (hevi i).comp hfst
  -- deterministic a.e. bound sqrt D <= A / gap
  have hsq : ∀ᵐ S ∂Q, Real.sqrt (D S) ≤ A S / gap := by
    filter_upwards [H1] with S hS
    apply sqrt_le_of_quad _ _ _ (hD0 S) hgap (hA0 S)
    refine hS.trans ?_
    have h1 : ∑ i, (a (S i) - F S (S i)) ≤ ∑ i, L (S i) * Real.sqrt (D S) :=
      Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hlip S (S i))
    have h2 : |∫ z, (a z - F S z) ∂P| ≤ c * Real.sqrt (D S) := by
      refine (abs_integral_le_integral_abs).trans ?_
      rw [hc, ← integral_mul_const]
      exact integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) (hL1.mul_const _)
        (ae_of_all _ fun z => hlip S z)
    have h3 := neg_le_abs (∫ z, (a z - F S z) ∂P)
    have h4 : (1 / (m : ℝ)) * ∑ i, (a (S i) - F S (S i))
        ≤ (1 / (m : ℝ)) * ∑ i, L (S i) * Real.sqrt (D S) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : A S * Real.sqrt (D S)
        = (1 / (m : ℝ)) * ∑ i, L (S i) * Real.sqrt (D S) + c * Real.sqrt (D S) := by
      simp only [hA, ← Finset.sum_mul]; ring
    rw [h5]; linarith
  have hDi : Integrable D₂ Q := by
    have hB2 : Integrable (fun S => (A S / gap) ^ 2) Q :=
      (hA2.div_const (gap ^ 2)).congr (ae_of_all _ fun S => by ring)
    refine Integrable.mono' hB2 hD2m ?_
    filter_upwards [hsq] with S hS
    rw [Real.norm_eq_abs, abs_of_nonneg (hD20 S)]
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hS 2
    rw [Real.sq_sqrt (hD0 S)] at this
    exact (hD2le S).trans this
  refine ⟨hDi, ?_⟩
  set g : (Fin m → Ω) → Ω → ℝ := fun S z => a z - F S z with hg
  have hgm : Measurable (Function.uncurry g) := by
    have := (ha.comp measurable_snd).sub hF
    exact this
  have hB : Integrable (fun p : (Fin m → Ω) × Ω => L p.2 ^ 2 + (A p.1 / gap) ^ 2) (Q.prod P) := by
    have h1 : Integrable (fun p : (Fin m → Ω) × Ω => L p.2 ^ 2) (Q.prod P) :=
      integrable_comp_mp hsnd hLL
    have h2 : Integrable (fun S => (A S / gap) ^ 2) Q :=
      (hA2.div_const (gap ^ 2)).congr (ae_of_all _ fun S => by ring)
    have h3 : Integrable (fun p : (Fin m → Ω) × Ω => (A p.1 / gap) ^ 2) (Q.prod P) :=
      integrable_comp_mp hfst h2
    exact h1.add h3
  have hsqP : ∀ᵐ p ∂(Q.prod P), Real.sqrt (D p.1) ≤ A p.1 / gap :=
    hfst.quasiMeasurePreserving.ae hsq
  have hGint : Integrable (Function.uncurry g) (Q.prod P) := by
    refine Integrable.mono' hB hgm.aestronglyMeasurable ?_
    filter_upwards [hsqP] with p hp
    rw [Real.norm_eq_abs]
    show |a p.2 - F p.1 p.2| ≤ _
    have h1 := hlip p.1 p.2
    have h2 : L p.2 * Real.sqrt (D p.1) ≤ L p.2 * (A p.1 / gap) :=
      mul_le_mul_of_nonneg_left hp (hL0 _)
    nlinarith [sq_nonneg (L p.2 - A p.1 / gap), mul_nonneg (hL0 p.2) (div_nonneg (hA0 p.1) hgap.le)]
  have hgi : ∀ i : Fin m, Integrable (fun S : Fin m → Ω => g S (S i)) Q := by
    intro i
    have hB1 : Integrable (fun S : Fin m → Ω => L (S i) ^ 2) Q := integrable_comp_mp (hevi i) hLL
    have hB2 : Integrable (fun S => (A S / gap) ^ 2) Q :=
      (hA2.div_const (gap ^ 2)).congr (ae_of_all _ fun S => by ring)
    have hB' : Integrable (fun S : Fin m → Ω => L (S i) ^ 2 + (A S / gap) ^ 2) Q := hB1.add hB2
    have hmeas : Measurable (fun S : Fin m → Ω => g S (S i)) :=
      hgm.comp (measurable_id.prodMk (measurable_pi_apply i))
    refine Integrable.mono' hB' hmeas.aestronglyMeasurable ?_
    filter_upwards [hsq] with S hp
    rw [Real.norm_eq_abs]
    show |a (S i) - F S (S i)| ≤ _
    have h1 := hlip S (S i)
    have h2 : L (S i) * Real.sqrt (D S) ≤ L (S i) * (A S / gap) :=
      mul_le_mul_of_nonneg_left hp (hL0 _)
    nlinarith [sq_nonneg (L (S i) - A S / gap), mul_nonneg (hL0 (S i)) (div_nonneg (hA0 S) hgap.le)]
  have hswapI : ∀ i : Fin m, Integrable
      (fun p : (Fin m → Ω) × Ω => g (Function.update p.1 i p.2) (p.1 i)) (Q.prod P) :=
    fun i => integrable_comp_mp (swap_mp P i) hGint
  have hswapE : ∀ i : Fin m, ∫ p, g (Function.update p.1 i p.2) (p.1 i) ∂(Q.prod P)
      = ∫ p, g p.1 p.2 ∂(Q.prod P) :=
    fun i => integral_comp_mp (swap_mp P i) hgm.aestronglyMeasurable
  have hfstI : ∀ i : Fin m, Integrable (fun p : (Fin m → Ω) × Ω => g p.1 (p.1 i)) (Q.prod P) :=
    fun i => integrable_comp_mp hfst (hgi i)
  have hfstE : ∀ i : Fin m, ∫ p, g p.1 (p.1 i) ∂(Q.prod P) = ∫ S, g S (S i) ∂Q :=
    fun i => integral_comp_mp hfst (hgi i).aestronglyMeasurable
  have hprodE : ∫ p, g p.1 p.2 ∂(Q.prod P) = ∫ S, ∫ z, g S z ∂P ∂Q := integral_prod _ hGint
  have hLs : ∫ p, L p.2 ^ 2 ∂(Q.prod P) = ∫ z, L z ^ 2 ∂P :=
    integral_comp_mp hsnd hLL.aestronglyMeasurable
  have hstep : ∀ i : Fin m, ∫ S, g S (S i) ∂Q - ∫ S, ∫ z, g S z ∂P ∂Q
      ≤ 2 * (∫ z, L z ^ 2 ∂P) / (m * gap) := by
    intro i
    have hLi : ∫ p, L (p.1 i) ^ 2 ∂(Q.prod P) = ∫ z, L z ^ 2 ∂P :=
      integral_comp_mp (hpi i) hLL.aestronglyMeasurable
    have hI1 : Integrable (fun p : (Fin m → Ω) × Ω => 3 * L (p.1 i) ^ 2) (Q.prod P) :=
      (integrable_comp_mp (hpi i) hLL).const_mul 3
    have hI2 : Integrable (fun p : (Fin m → Ω) × Ω => L p.2 ^ 2) (Q.prod P) :=
      integrable_comp_mp hsnd hLL
    have hbd : Integrable (fun p : (Fin m → Ω) × Ω =>
        (3 * L (p.1 i) ^ 2 + L p.2 ^ 2) / (2 * (m * gap))) (Q.prod P) :=
      (hI1.add hI2).div_const _
    have hdiff : Integrable (fun p : (Fin m → Ω) × Ω =>
        g p.1 (p.1 i) - g (Function.update p.1 i p.2) (p.1 i)) (Q.prod P) :=
      (hfstI i).sub (hswapI i)
    rw [← hfstE i, ← hprodE, ← hswapE i, ← integral_sub (hfstI i) (hswapI i)]
    refine (integral_mono_ae hdiff hbd ?_).trans ?_
    · filter_upwards [Hstab i] with p hp
      show (a (p.1 i) - F p.1 (p.1 i)) - (a (p.1 i) - F (Function.update p.1 i p.2) (p.1 i)) ≤ _
      have hmg : 0 < (m : ℝ) * gap := mul_pos hmpos hgap
      have hq : L (p.1 i) * (L (p.1 i) + L p.2) ≤ (3 * L (p.1 i) ^ 2 + L p.2 ^ 2) / 2 := by
        nlinarith [sq_nonneg (L (p.1 i) - L p.2)]
      calc (a (p.1 i) - F p.1 (p.1 i)) - (a (p.1 i) - F (Function.update p.1 i p.2) (p.1 i))
          = F (Function.update p.1 i p.2) (p.1 i) - F p.1 (p.1 i) := by ring
        _ ≤ L (p.1 i) * (L (p.1 i) + L p.2) / (m * gap) := hp
        _ ≤ (3 * L (p.1 i) ^ 2 + L p.2 ^ 2) / 2 / (m * gap) := div_le_div_of_nonneg_right hq hmg.le
        _ = (3 * L (p.1 i) ^ 2 + L p.2 ^ 2) / (2 * (m * gap)) := by rw [div_div]
    · rw [integral_div, integral_add hI1 hI2, integral_const_mul, hLi, hLs]
      apply le_of_eq; ring
  have hsumI : Integrable (fun S : Fin m → Ω => ∑ i, g S (S i)) Q :=
    integrable_finsetSum _ fun i _ => hgi i
  have hint2 : Integrable (fun S => ∫ z, g S z ∂P) Q := hGint.integral_prod_left
  have hTint : Integrable (fun S => (1 / (m : ℝ)) * ∑ i, g S (S i) - ∫ z, g S z ∂P) Q :=
    (hsumI.const_mul _).sub hint2
  have H1' : ∀ᵐ S ∂Q, gap * D₂ S ≤ (1 / (m : ℝ)) * ∑ i, g S (S i) - ∫ z, g S z ∂P := by
    filter_upwards [H1] with S hS
    exact (mul_le_mul_of_nonneg_left (hD2le S) hgap.le).trans hS
  calc gap * ∫ S, D₂ S ∂Q = ∫ S, gap * D₂ S ∂Q := (integral_const_mul _ _).symm
    _ ≤ ∫ S, ((1 / (m : ℝ)) * ∑ i, g S (S i) - ∫ z, g S z ∂P) ∂Q :=
        integral_mono_ae (hDi.const_mul _) hTint H1'
    _ = (1 / (m : ℝ)) * ∑ i, (∫ S, g S (S i) ∂Q - ∫ S, ∫ z, g S z ∂P ∂Q) := by
        rw [integral_sub (hsumI.const_mul _) hint2, integral_const_mul,
          integral_finsetSum _ fun i _ => hgi i, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [mul_sub, ← mul_assoc, one_div_mul_cancel hmpos.ne', one_mul]
    _ ≤ (1 / (m : ℝ)) * ∑ _i : Fin m, 2 * (∫ z, L z ^ 2 ∂P) / (m * gap) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hstep i) (by positivity)
    _ = 2 * (∫ z, L z ^ 2 ∂P) / (m * gap) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, one_div_mul_cancel hmpos.ne', one_mul]

end S_F_bias

section S_B_exists
set_option autoImplicit false

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Limit step for a closed extended function along a sequence with bounded values. -/
theorem closed_seq (h : ExtFn E) (hc : h.IsClosed) (v : ℕ → E) (a : E)
    (hv : Tendsto v atTop (𝓝 a)) (hdom : ∀ n, v n ∈ h.dom) (M : ℝ)
    (hM : ∀ n, h.val (v n) ≤ M) :
    a ∈ h.dom ∧ ∀ ε > 0, ∀ᶠ n in atTop, h.val a - ε < h.val (v n) := by
  unfold ExtFn.IsClosed at hc
  have ha : a ∈ h.dom := by
    by_contra hna
    have h1 := hv.eventually (hc a (M : EReal) (by simp only [if_neg hna]; exact EReal.coe_lt_top M))
    obtain ⟨n, hn⟩ := h1.exists
    simp only [if_pos (hdom n)] at hn
    exact absurd (EReal.coe_lt_coe_iff.mp hn) (not_lt.mpr (hM n))
  refine ⟨ha, fun ε hε => ?_⟩
  have h1 := hv.eventually (hc a ((h.val a - ε : ℝ) : EReal)
    (by simp only [if_pos ha]; exact EReal.coe_lt_coe_iff.mpr (by linarith)))
  filter_upwards [h1] with n hn
  simp only [if_pos (hdom n)] at hn
  exact EReal.coe_lt_coe_iff.mp hn

theorem clm_abs_le (ℓ : E →L[ℝ] ℝ) (v : E) : |ℓ v| ≤ ‖ℓ‖ * ‖v‖ := by
  have := ℓ.le_opNorm v
  rwa [Real.norm_eq_abs] at this

/-- Strong convexity at a fixed interior centre `u0` extends to boundary points of `dom Φ`. -/
theorem bregman_lower_ext (Φ g : ExtFn E) (α : ℝ) (u0 u : E)
    (hconv : ConvexOn ℝ Φ.dom Φ.val) (hgd : Convex ℝ g.dom)
    (hu0 : u0 ∈ g.dom) (hu0i : u0 ∈ interior Φ.dom)
    (hsc : ∀ x ∈ g.dom ∩ interior Φ.dom, α / 2 * ‖u0 - x‖ ^ 2 ≤ bregman Φ x u0)
    (hu : u ∈ g.dom ∩ Φ.dom) :
    α / 2 * ‖u - u0‖ ^ 2 ≤ bregman Φ u u0 := by
  have hstep : ∀ t ∈ Set.Ioo (0:ℝ) 1, α / 2 * t * ‖u - u0‖ ^ 2 ≤ bregman Φ u u0 := by
    intro t ht
    have hw' : u0 + t • (u - u0) = (1 - t) • u0 + t • u := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have hwg : u0 + t • (u - u0) ∈ g.dom := by
      rw [hw']; exact hgd hu0 hu.1 (by linarith [ht.2]) ht.1.le (by ring)
    have hwi : u0 + t • (u - u0) ∈ interior Φ.dom := by
      have hseg := hconv.1.openSegment_interior_self_subset_interior hu0i hu.2
      exact hseg ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, hw'.symm⟩
    have hcv := hconv.2 (interior_subset hu0i) hu.2 (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)
      ht.1.le (by ring : (1 - t) + t = 1)
    rw [← hw', smul_eq_mul, smul_eq_mul] at hcv
    have hs := hsc _ ⟨hwg, hwi⟩
    unfold bregman at hs ⊢
    have e1 : u0 + t • (u - u0) - u0 = t • (u - u0) := by abel
    have e2 : u0 - (u0 + t • (u - u0)) = -(t • (u - u0)) := by abel
    rw [e1, e2, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, map_smul,
      smul_eq_mul] at hs
    have key : t * (α / 2 * t * ‖u - u0‖ ^ 2)
        ≤ t * (Φ.val u - Φ.val u0 - fderiv ℝ Φ.val u0 (u - u0)) := by nlinarith
    exact le_of_mul_le_mul_left key ht.1
  have hlim : Tendsto (fun t : ℝ => α / 2 * t * ‖u - u0‖ ^ 2) (𝓝[<] 1)
      (𝓝 (α / 2 * 1 * ‖u - u0‖ ^ 2)) :=
    ((continuous_const.mul continuous_id).mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[<] (1:ℝ), α / 2 * t * ‖u - u0‖ ^ 2 ≤ bregman Φ u u0 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with t ht using hstep t ht
  have := le_of_tendsto hlim hev
  simpa using this

theorem quad_bound (α A M N : ℝ) (hα : 0 < α) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (h : α / 2 * N ^ 2 - A * N ≤ M) : N ≤ 1 + 2 * (A + |M|) / α := by
  by_contra hc
  push Not at hc
  have hpos : 0 ≤ 2 * (A + |M|) / α := by positivity
  have hαR : α / 2 * (1 + 2 * (A + |M|) / α) = α / 2 + A + |M| := by field_simp; ring
  have h0 := mul_lt_mul_of_pos_left hc (by positivity : (0:ℝ) < α / 2)
  have h1 : α / 2 * N - A > |M| := by linarith
  have hN1 : 1 < N := by linarith
  have h2 : N * (α / 2 * N - A) > N * |M| := mul_lt_mul_of_pos_left h1 (by linarith)
  have h3 : N * |M| ≥ |M| := by nlinarith [abs_nonneg M]
  have h4 : |M| ≥ M := le_abs_self M
  nlinarith

/-- D4: existence of a Bregman proximal point (lsc + coercivity, finite dimension). -/
theorem prox_exists [FiniteDimensional ℝ E] (Φ g : ExtFn E) (α rhoBar b : ℝ) (u0 y : E)
    (hΦc : Φ.IsClosed) (hconv : ConvexOn ℝ Φ.dom Φ.val) (hgc : g.IsClosed)
    (hgd : Convex ℝ g.dom) (hgb : ∀ u ∈ g.dom, b ≤ g.val u)
    (hu0 : u0 ∈ g.dom) (hu0i : u0 ∈ interior Φ.dom)
    (hα : 0 < α) (hrb : 0 < rhoBar)
    (hsc : ∀ x ∈ g.dom ∩ interior Φ.dom, α / 2 * ‖u0 - x‖ ^ 2 ≤ bregman Φ x u0) :
    (proxSet Φ g rhoBar y).Nonempty := by
  have hu0K : u0 ∈ g.dom ∩ Φ.dom := ⟨hu0, interior_subset hu0i⟩
  set A := ‖fderiv ℝ Φ.val u0‖ + ‖fderiv ℝ Φ.val y‖ with hAdef
  have hA : 0 ≤ A := by positivity
  set c0 := Φ.val u0 - Φ.val y - fderiv ℝ Φ.val y (u0 - y) with hc0
  have hD : ∀ u ∈ g.dom ∩ Φ.dom,
      α / 2 * ‖u - u0‖ ^ 2 - A * ‖u - u0‖ + c0 ≤ bregman Φ u y := by
    intro u hu
    have h1 := bregman_lower_ext Φ g α u0 u hconv hgd hu0 hu0i hsc hu
    unfold bregman at h1 ⊢
    have e : fderiv ℝ Φ.val y (u - y) = fderiv ℝ Φ.val y (u - u0) + fderiv ℝ Φ.val y (u0 - y) := by
      rw [← map_add]; congr 1; abel
    have h2 := abs_le.mp (clm_abs_le (fderiv ℝ Φ.val u0) (u - u0))
    have h3 := abs_le.mp (clm_abs_le (fderiv ℝ Φ.val y) (u - u0))
    rw [e]
    linarith [h2.1, h3.2]
  set lbD := c0 - A ^ 2 / (2 * α) with hlbD
  have hDlb : ∀ u ∈ g.dom ∩ Φ.dom, lbD ≤ bregman Φ u y := by
    intro u hu
    have h := hD u hu
    have hsq : 0 ≤ (α * ‖u - u0‖ - A) ^ 2 / (2 * α) := by positivity
    have he : (α * ‖u - u0‖ - A) ^ 2 / (2 * α)
        = α / 2 * ‖u - u0‖ ^ 2 - A * ‖u - u0‖ + A ^ 2 / (2 * α) := by field_simp; ring
    linarith
  set G : E → ℝ := fun u => g.val u + rhoBar * bregman Φ u y with hG
  have hGlb : ∀ u ∈ g.dom ∩ Φ.dom, b + rhoBar * lbD ≤ G u := by
    intro u hu
    have := mul_le_mul_of_nonneg_left (hDlb u hu) hrb.le
    simp only [hG]; linarith [hgb u hu.1]
  have hne : (G '' (g.dom ∩ Φ.dom)).Nonempty := ⟨G u0, u0, hu0K, rfl⟩
  have hbdd : BddBelow (G '' (g.dom ∩ Φ.dom)) := ⟨b + rhoBar * lbD, by
    rintro _ ⟨u, hu, rfl⟩; exact hGlb u hu⟩
  set I := sInf (G '' (g.dom ∩ Φ.dom)) with hI
  have hIle : ∀ u ∈ g.dom ∩ Φ.dom, I ≤ G u := fun u hu => csInf_le hbdd ⟨u, hu, rfl⟩
  have hseq : ∀ n : ℕ, ∃ u ∈ g.dom ∩ Φ.dom, G u < I + 1 / ((n:ℝ) + 1) := by
    intro n
    have hp : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (show I < I + 1 / ((n:ℝ) + 1) by
      linarith)
    exact ⟨u, hu, hlt⟩
  choose u huK huG using hseq
  have hGu1 : ∀ n, G (u n) ≤ G u0 + 1 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have := n.cast_nonneg (α := ℝ); linarith
    linarith [huG n, hIle u0 hu0K]
  -- boundedness
  set M2 := (G u0 + 1 - b) / rhoBar - c0 with hM2
  set R := 1 + 2 * (A + |M2|) / α with hR
  have hball : ∀ n, u n ∈ Metric.closedBall u0 R := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply quad_bound α A M2 _ hα hA (norm_nonneg _)
    have h1 := hD (u n) (huK n)
    have h2 := hGu1 n
    have h3 := hgb (u n) (huK n).1
    simp only [hG] at h2
    have h4 : rhoBar * bregman Φ (u n) y ≤ G u0 + 1 - b := by linarith
    have h5 : bregman Φ (u n) y ≤ (G u0 + 1 - b) / rhoBar := by
      rw [le_div_iff₀ hrb]; linarith
    simp only [hM2]; linarith
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hball
  -- bounds along the subsequence
  have hgM : ∀ k, g.val (u (φ k)) ≤ G u0 + 1 - rhoBar * lbD := by
    intro k
    have h1 := mul_le_mul_of_nonneg_left (hDlb _ (huK (φ k))) hrb.le
    have h2 := hGu1 (φ k)
    simp only [hG] at h2; linarith
  have hΦM : ∀ k, Φ.val (u (φ k)) ≤ (G u0 + 1 - b) / rhoBar + Φ.val y
      + ‖fderiv ℝ Φ.val y‖ * (R + ‖u0 - y‖) := by
    intro k
    have h2 := hGu1 (φ k)
    have h3 := hgb _ (huK (φ k)).1
    simp only [hG] at h2
    have h5 : bregman Φ (u (φ k)) y ≤ (G u0 + 1 - b) / rhoBar := by
      rw [le_div_iff₀ hrb]; linarith
    unfold bregman at h5
    have h6 := (abs_le.mp (clm_abs_le (fderiv ℝ Φ.val y) (u (φ k) - y))).2
    have h7 : ‖u (φ k) - y‖ ≤ R + ‖u0 - y‖ := by
      have hb := hball (φ k)
      rw [Metric.mem_closedBall, dist_eq_norm] at hb
      calc ‖u (φ k) - y‖ = ‖(u (φ k) - u0) + (u0 - y)‖ := by congr 1; abel
        _ ≤ ‖u (φ k) - u0‖ + ‖u0 - y‖ := norm_add_le _ _
        _ ≤ R + ‖u0 - y‖ := by linarith
    have h8 := mul_le_mul_of_nonneg_left h7 (norm_nonneg (fderiv ℝ Φ.val y))
    linarith
  obtain ⟨hag, hag'⟩ := closed_seq g hgc (u ∘ φ) a hlim (fun k => (huK (φ k)).1) _ hgM
  obtain ⟨haΦ, haΦ'⟩ := closed_seq Φ hΦc (u ∘ φ) a hlim (fun k => (huK (φ k)).2) _ hΦM
  have haK : a ∈ g.dom ∩ Φ.dom := ⟨hag, haΦ⟩
  have hlin : Tendsto (fun k => fderiv ℝ Φ.val y ((u ∘ φ) k - y)) atTop
      (𝓝 (fderiv ℝ Φ.val y (a - y))) :=
    ((fderiv ℝ Φ.val y).continuous.tendsto _).comp (hlim.sub_const y)
  have hinv : Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hGa : G a ≤ I := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    set ε' := ε / (3 * (1 + rhoBar)) with hε'
    have hε'p : 0 < ε' := by positivity
    have hε'e : ε' * (2 + 2 * rhoBar) < ε := by
      rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    have ev1 := hag' ε' hε'p
    have ev2 := haΦ' ε' hε'p
    have ev3 := hlin.eventually (Metric.ball_mem_nhds _ hε'p)
    have ev4 := (tendsto_order.1 hinv).2 ε' hε'p
    obtain ⟨k, h1, h2, h3, h4⟩ := (ev1.and (ev2.and (ev3.and ev4))).exists
    simp only [Function.comp] at h1 h2 h3
    rw [Real.dist_eq] at h3
    have h3' := (abs_lt.mp h3).2
    have hk : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((k:ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have := hφ.id_le k
      have : (k:ℝ) ≤ (φ k : ℝ) := by exact_mod_cast this
      linarith
    have hGk := huG (φ k)
    simp only [hG] at hGk ⊢
    unfold bregman at hGk ⊢
    have hm2 := mul_lt_mul_of_pos_left h2 hrb
    have hm3 := mul_lt_mul_of_pos_left h3' hrb
    nlinarith
  refine ⟨a, haK, isMinOn_iff.2 (fun v hv => ?_)⟩
  exact hGa.trans (hIle v hv)

end S_B_exists

section S_C_meas
set_option autoImplicit false

open Filter Topology MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example [FiniteDimensional ℝ E] : SecondCountableTopology E := inferInstance

/-- A countable subset of `K` that is dense in the graph of `h` over `K`. -/
theorem graph_dense [SecondCountableTopology E] (K : Set E) (h : E → ℝ) :
    ∃ Q ⊆ K, Q.Countable ∧ ∀ u ∈ K, ∀ δ > 0, ∃ q ∈ Q, dist q u < δ ∧ |h q - h u| < δ := by
  set Γ : Set (E × ℝ) := (fun u => (u, h u)) '' K with hΓ
  obtain ⟨t, htΓ, htc, hΓt⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace Γ).exists_countable_dense_subset
  refine ⟨Prod.fst '' t, ?_, htc.image _, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨u, hu, rfl⟩ := htΓ hp
    exact hu
  · intro u hu δ hδ
    have hmem : (u, h u) ∈ closure t := hΓt ⟨u, hu, rfl⟩
    obtain ⟨p, hpt, hpd⟩ := Metric.mem_closure_iff.mp hmem δ hδ
    obtain ⟨v, -, rfl⟩ := htΓ hpt
    rw [Prod.dist_eq, max_lt_iff] at hpd
    refine ⟨v, ⟨(v, h v), hpt, rfl⟩, ?_, ?_⟩
    · rw [dist_comm]; exact hpd.1
    · rw [← Real.dist_eq, dist_comm]; exact hpd.2

/-- Approximating `F + h` from above on the countable graph-dense set, `F` continuous on `K`. -/
theorem graph_approx (K : Set E) (F h : E → ℝ) (hF : ContinuousOn F K) (Q : Set E)
    (hQK : Q ⊆ K) (hQ : ∀ u ∈ K, ∀ δ > 0, ∃ q ∈ Q, dist q u < δ ∧ |h q - h u| < δ) :
    ∀ u ∈ K, ∀ ε > 0, ∃ q ∈ Q, F q + h q < F u + h u + ε := by
  intro u hu ε hε
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousWithinAt_iff.mp (hF u hu) (ε / 2) (by linarith)
  obtain ⟨q, hqQ, hqd, hqh⟩ := hQ u hu (min δ (ε / 2)) (lt_min hδ (by linarith))
  have h1 := hδF (hQK hqQ) (lt_of_lt_of_le hqd (min_le_left _ _))
  rw [Real.dist_eq] at h1
  have h2 := lt_of_lt_of_le hqh (min_le_right _ _)
  refine ⟨q, hqQ, ?_⟩
  linarith [(abs_lt.mp h1).2, (abs_lt.mp h2).2]

/-- D5 core: the minimizer of a Carathéodory objective with quadratic growth is measurable
(membership in any closed set is a measurable event on the good set). -/
theorem meas_of_growth [SecondCountableTopology E] {Ω' : Type*} [MeasurableSpace Ω']
    (K : Set E) (F : Ω' → E → ℝ) (h : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hF : ∀ ω, ContinuousOn (F ω) K) (hFm : ∀ u, Measurable (fun ω => F ω u))
    (Good : Set Ω') (hGood : MeasurableSet Good) (x : Ω' → E)
    (hxK : ∀ ω ∈ Good, x ω ∈ K)
    (hgrow : ∀ ω ∈ Good, ∀ u ∈ K, F ω (x ω) + h (x ω) + c * ‖u - x ω‖ ^ 2 ≤ F ω u + h u)
    (B : Set E) (hB : IsClosed B) :
    MeasurableSet {ω | ω ∈ Good ∧ x ω ∈ B} := by
  obtain ⟨QK, hQKK, hQKc, hQK⟩ := graph_dense K h
  obtain ⟨QB, hQBK, hQBc, hQB⟩ := graph_dense (K ∩ B) h
  have heq : {ω | ω ∈ Good ∧ x ω ∈ B} = Good ∩ ⋂ n : ℕ, ⋃ q ∈ QB, ⋂ q' ∈ QK,
      {ω | F ω q + h q < F ω q' + h q' + 1 / ((n:ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
    constructor
    · rintro ⟨hω, hxB⟩
      refine ⟨hω, fun n => ?_⟩
      have hε : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      obtain ⟨q, hq, hlt⟩ := graph_approx (K ∩ B) (F ω) h ((hF ω).mono Set.inter_subset_left)
        QB hQBK hQB (x ω) ⟨hxK ω hω, hxB⟩ _ hε
      refine ⟨q, hq, fun q' hq' => ?_⟩
      have := hgrow ω hω q' (hQKK hq')
      have hsq : 0 ≤ c * ‖q' - x ω‖ ^ 2 := by positivity
      linarith
    · rintro ⟨hω, hall⟩
      refine ⟨hω, ?_⟩
      by_contra hxB
      have hopen : IsOpen Bᶜ := hB.isOpen_compl
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (x ω) hxB
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < c * r ^ 2 / 2 by positivity)
      obtain ⟨q, hq, hq'⟩ := hall n
      obtain ⟨q', hq'Q, hlt⟩ := graph_approx K (F ω) h (hF ω) QK hQKK hQK (x ω) (hxK ω hω)
        (1 / ((n:ℝ) + 1)) (by positivity)
      have h1 := hq' q' hq'Q
      have hqKB := hQBK hq
      have h2 := hgrow ω hω q hqKB.1
      have hr' : r ≤ ‖q - x ω‖ := by
        by_contra hlt'
        push Not at hlt'
        have : q ∈ Metric.ball (x ω) r := by rw [Metric.mem_ball, dist_eq_norm]; exact hlt'
        exact hball this hqKB.2
      have h3 : c * r ^ 2 ≤ c * ‖q - x ω‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact pow_le_pow_left₀ hr.le hr' 2
      linarith
  rw [heq]
  refine hGood.inter (MeasurableSet.iInter fun n => ?_)
  refine MeasurableSet.biUnion hQBc fun q _ => MeasurableSet.biInter hQKc fun q' _ => ?_
  exact measurableSet_lt ((hFm q).add_const _) (((hFm q').add_const _).add_const _)

/-- D5 packaged: the distance of the good-set minimizer to a fixed point is measurable. -/
theorem meas_dist_of_growth [SecondCountableTopology E] {Ω' : Type*} [MeasurableSpace Ω']
    (K : Set E) (F : Ω' → E → ℝ) (h : E → ℝ) (c : ℝ) (hc : 0 < c)
    (hF : ∀ ω, ContinuousOn (F ω) K) (hFm : ∀ u, Measurable (fun ω => F ω u))
    (Good : Set Ω') (hGood : MeasurableSet Good) (x : Ω' → E)
    (hxK : ∀ ω ∈ Good, x ω ∈ K)
    (hgrow : ∀ ω ∈ Good, ∀ u ∈ K, F ω (x ω) + h (x ω) + c * ‖u - x ω‖ ^ 2 ≤ F ω u + h u)
    (p : E) :
    Measurable (Good.indicator (fun ω => ‖x ω - p‖)) := by
  refine measurable_of_Iic fun a => ?_
  have heq : Good.indicator (fun ω => ‖x ω - p‖) ⁻¹' Set.Iic a
      = {ω | ω ∈ Good ∧ x ω ∈ Metric.closedBall p a} ∪ (Goodᶜ ∩ {_ω | (0:ℝ) ≤ a}) := by
    ext ω
    by_cases hω : ω ∈ Good
    · simp [Set.indicator_of_mem hω, hω, dist_eq_norm]
    · simp [Set.indicator_of_notMem hω, hω]
  rw [heq]
  refine (meas_of_growth K F h c hc hF hFm Good hGood x hxK hgrow _
    Metric.isClosed_closedBall).union (hGood.compl.inter ?_)
  exact MeasurableSet.const _

end S_C_meas

section S_E_risk
set_option autoImplicit false

open Filter Topology MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closed_elim (g : ExtFn E) (hg : g.IsClosed) (a : E) :
    (a ∈ g.dom → ∀ ε > 0, ∀ᶠ x in 𝓝 a, x ∈ g.dom → g.val a - ε < g.val x) ∧
    (a ∉ g.dom → ∀ M : ℝ, ∀ᶠ x in 𝓝 a, x ∈ g.dom → M < g.val x) := by
  unfold ExtFn.IsClosed at hg
  constructor
  · intro ha ε hε
    have h1 := hg a ((g.val a - ε : ℝ) : EReal)
      (by simp only [if_pos ha]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
    filter_upwards [h1] with x hx hxd
    simp only [if_pos hxd] at hx
    exact EReal.coe_lt_coe_iff.mp hx
  · intro ha M
    have h1 := hg a (M : EReal) (by simp only [if_neg ha]; exact EReal.coe_lt_top M)
    filter_upwards [h1] with x hx hxd
    simp only [if_pos hxd] at hx
    exact EReal.coe_lt_coe_iff.mp hx

theorem closed_intro (g : ExtFn E)
    (h1 : ∀ a ∈ g.dom, ∀ ε > 0, ∀ᶠ x in 𝓝 a, x ∈ g.dom → g.val a - ε < g.val x)
    (h2 : ∀ a ∉ g.dom, ∀ M : ℝ, ∀ᶠ x in 𝓝 a, x ∈ g.dom → M < g.val x) : g.IsClosed := by
  unfold ExtFn.IsClosed
  intro a y hy
  by_cases ha : a ∈ g.dom
  · simp only [if_pos ha] at hy
    induction y using EReal.rec with
    | bot =>
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ g.dom
      · simp only [if_pos hx]; exact EReal.bot_lt_coe _
      · simp only [if_neg hx]; exact bot_lt_top
    | top => exact absurd hy (not_lt.mpr le_top)
    | coe y =>
      have hy' : y < g.val a := EReal.coe_lt_coe_iff.mp hy
      filter_upwards [h1 a ha (g.val a - y) (by linarith)] with x hx
      by_cases hxd : x ∈ g.dom
      · simp only [if_pos hxd]; exact EReal.coe_lt_coe_iff.mpr (by have := hx hxd; linarith)
      · simp only [if_neg hxd]; exact EReal.coe_lt_top y
  · simp only [if_neg ha] at hy
    induction y using EReal.rec with
    | bot =>
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ g.dom
      · simp only [if_pos hx]; exact EReal.bot_lt_coe _
      · simp only [if_neg hx]; exact bot_lt_top
    | top => exact absurd hy (lt_irrefl _)
    | coe y =>
      filter_upwards [h2 a ha y] with x hx
      by_cases hxd : x ∈ g.dom
      · simp only [if_pos hxd]; exact EReal.coe_lt_coe_iff.mpr (hx hxd)
      · simp only [if_neg hxd]; exact EReal.coe_lt_top y

theorem empRisk_eq_avg {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m)
    (r : ExtFn E) (f : E → Ω → ℝ) (S : Fin m → Ω) (x : E) :
    (empRisk r f S).val x = (1 / (m:ℝ)) * ∑ i, (sampleFn r f (S i)).val x := by
  simp only [empRisk, sampleFn, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [mul_add (1 / (m:ℝ)), ← mul_assoc, one_div_mul_cancel this, one_mul]

theorem empRisk_weaklyConvex {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m)
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (ρ : ℝ) (S : Fin m → Ω)
    (hS : ∀ i, WeaklyConvexRel Φ (sampleFn r f (S i)) ρ) :
    WeaklyConvexRel Φ (empRisk r f S) ρ := by
  unfold WeaklyConvexRel at hS ⊢
  change ConvexOn ℝ (r.dom ∩ Φ.dom) _
  have hS' : ∀ i, ConvexOn ℝ (r.dom ∩ Φ.dom)
      (fun x => (sampleFn r f (S i)).val x + ρ * Φ.val x) := hS
  have hconv : Convex ℝ (r.dom ∩ Φ.dom) := (hS' ⟨0, hm⟩).1
  have hsum : ConvexOn ℝ (r.dom ∩ Φ.dom)
      (∑ i, fun x => (sampleFn r f (S i)).val x + ρ * Φ.val x) :=
    Finset.sum_induction _ (fun F => ConvexOn ℝ (r.dom ∩ Φ.dom) F) (fun a b ha hb => ha.add hb)
      (convexOn_const 0 hconv) (fun i _ => hS' i)
  have hsm := hsum.smul (show (0:ℝ) ≤ 1 / (m:ℝ) by positivity)
  refine hsm.congr (fun x _ => ?_)
  have : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Finset.sum_apply, smul_eq_mul, empRisk_eq_avg hm,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_add (1 / (m:ℝ)), ← mul_assoc (1 / (m:ℝ)) (m:ℝ), one_div_mul_cancel this, one_mul]

theorem empRisk_closed {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m)
    (r : ExtFn E) (f : E → Ω → ℝ) (S : Fin m → Ω)
    (hS : ∀ i, (sampleFn r f (S i)).IsClosed) : (empRisk r f S).IsClosed := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  apply closed_intro
  · intro a ha ε hε
    have hev : ∀ᶠ x in 𝓝 a, ∀ i, x ∈ r.dom →
        (sampleFn r f (S i)).val a - ε < (sampleFn r f (S i)).val x :=
      Filter.eventually_all.2 fun i => (closed_elim _ (hS i) a).1 ha ε hε
    filter_upwards [hev] with x hx hxd
    rw [empRisk_eq_avg hm, empRisk_eq_avg hm]
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hx i hxd)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hlt
    have := mul_lt_mul_of_pos_left hlt (show (0:ℝ) < 1 / m by positivity)
    rw [mul_sub, ← mul_assoc, one_div_mul_cancel hmR.ne', one_mul] at this
    linarith
  · intro a ha M
    have hev : ∀ᶠ x in 𝓝 a, ∀ i, x ∈ r.dom → M < (sampleFn r f (S i)).val x :=
      Filter.eventually_all.2 fun i => (closed_elim _ (hS i) a).2 ha M
    filter_upwards [hev] with x hx hxd
    rw [empRisk_eq_avg hm]
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hx i hxd)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
    have := mul_lt_mul_of_pos_left hlt (show (0:ℝ) < 1 / m by positivity)
    rw [← mul_assoc, one_div_mul_cancel hmR.ne', one_mul] at this
    linarith

theorem empRisk_lb {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (hm : 0 < m)
    (r : ExtFn E) (f : E → Ω → ℝ) (S : Fin m → Ω)
    (hS : ∀ i, BddBelow ((sampleFn r f (S i)).val '' r.dom)) :
    ∃ b : ℝ, ∀ u ∈ r.dom, b ≤ (empRisk r f S).val u := by
  choose b hb using hS
  refine ⟨(1 / (m:ℝ)) * ∑ i, b i, fun u hu => ?_⟩
  rw [empRisk_eq_avg hm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun i _ => hb i ⟨u, hu, rfl⟩

end S_E_risk

section S_G_meas
set_option autoImplicit false

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem measurable_of_norm_sub [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {X : Type*} [MeasurableSpace X] (x : X → E)
    (hd : ∀ p, Measurable (fun ω => ‖x ω - p‖)) : Measurable x := by
  refine measurable_of_isOpen fun U hU => ?_
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : {q : E × ℝ // Metric.ball q.1 q.2 ⊆ U} => Metric.ball i.1.1 i.1.2)
    (fun i => Metric.isOpen_ball)
  have hU' : U = ⋃ i : {q : E × ℝ // Metric.ball q.1 q.2 ⊆ U}, Metric.ball i.1.1 i.1.2 := by
    ext y; constructor
    · intro hy
      obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU y hy
      exact Set.mem_iUnion.2 ⟨⟨(y, ε), hb⟩, Metric.mem_ball_self hε⟩
    · intro hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      exact i.2 hi
  rw [hU', ← hTU, Set.preimage_iUnion₂]
  refine MeasurableSet.biUnion hTc fun i _ => ?_
  have : x ⁻¹' Metric.ball i.1.1 i.1.2 = {ω | ‖x ω - i.1.1‖ < i.1.2} := by
    ext ω; simp [dist_eq_norm]
  rw [this]
  exact measurableSet_lt (hd _) measurable_const

theorem carath_meas [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (K : Set E) (f : E → Z → ℝ) (hc : ∀ z, ContinuousOn (fun u => f u z) K)
    (hm : ∀ u, Measurable (f u)) (x : X → E) (hx : Measurable x) (hxK : ∀ ω, x ω ∈ K) :
    Measurable (fun p : X × Z => f (x p.1) p.2) := by
  let u : K → Z → ℝ := fun k z => f k z
  have hu : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable (fun z => (hc z).restrict) (fun k => hm k)
  have hxk : Measurable (fun ω => (⟨x ω, hxK ω⟩ : K)) := hx.subtype_mk
  exact hu.comp (hxk.prodMap measurable_id)

end S_G_meas

section S_H_cont
set_option autoImplicit false

open Filter Topology MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rockafellar Lemma 26.2 (form used here): at a point `p ∈ dom Φ \ int dom Φ` of a Legendre
function, the slope of `Φ` along the segment towards an interior point `u` is unbounded below. -/
theorem grad_local_bound [FiniteDimensional ℝ E] (Φ : ExtFn E) (hconv : ConvexOn ℝ Φ.dom Φ.val)
    (hdiff : DifferentiableOn ℝ Φ.val (interior Φ.dom)) (y0 : E) (hy0 : y0 ∈ interior Φ.dom) :
    ∃ r > 0, ∃ B : ℝ, ∀ x ∈ Metric.ball y0 r, ‖fderiv ℝ Φ.val x‖ ≤ B := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y0 hy0
  have hcb : Metric.closedBall y0 (ε / 2) ⊆ interior Φ.dom := fun z hz => by
    apply hball; rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hz; linarith
  have hcont : ContinuousOn Φ.val (Metric.closedBall y0 (ε / 2)) := hdiff.continuousOn.mono hcb
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall y0 (ε / 2)).bddAbove_image hcont
  obtain ⟨c0, hc0⟩ := (isCompact_closedBall y0 (ε / 2)).bddBelow_image hcont
  refine ⟨ε / 4, by linarith, (C0 - c0) / (ε / 4), fun x hx => ?_⟩
  have hxc : x ∈ Metric.closedBall y0 (ε / 2) := by
    rw [Metric.mem_closedBall]; rw [Metric.mem_ball] at hx; linarith
  have hxi := hcb hxc
  have hdx : DifferentiableAt ℝ Φ.val x :=
    (hdiff x hxi).differentiableAt (isOpen_interior.mem_nhds hxi)
  apply opNorm_le_of_ball_bound _ _ _ (by linarith)
  intro w hw
  have hxw : x + w ∈ Metric.closedBall y0 (ε / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; rw [Metric.mem_ball, dist_eq_norm] at hx
    calc ‖x + w - y0‖ = ‖(x - y0) + w‖ := by congr 1; abel
      _ ≤ ‖x - y0‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ε / 2 := by linarith
  have h1 := convex_fderiv_le Φ.val Φ.dom hconv x (x + w) (interior_subset hxi)
    (interior_subset (hcb hxw)) hdx
  rw [add_sub_cancel_left] at h1
  have h2 : Φ.val (x + w) ≤ C0 := hC0 (Set.mem_image_of_mem _ hxw)
  have h3 : c0 ≤ Φ.val x := hc0 (Set.mem_image_of_mem _ hxc)
  linarith

theorem f_contOn [FiniteDimensional ℝ E] {Z : Type*} (Φ : ExtFn E) (K : Set E)
    (hK : K ⊆ interior Φ.dom) (hconv : ConvexOn ℝ Φ.dom Φ.val)
    (hdiff : DifferentiableOn ℝ Φ.val (interior Φ.dom)) (f : E → Z → ℝ) (L : Z → ℝ)
    (hL0 : ∀ z, 0 ≤ L z)
    (hlip : ∀ x ∈ K, ∀ y ∈ K, ∀ z, |f x z - f y z| ≤ L z * Real.sqrt (bregmanSym Φ x y))
    (z : Z) : ContinuousOn (fun u => f u z) K := by
  intro y0 hy0
  obtain ⟨r, hr, B, hB⟩ := grad_local_bound Φ hconv hdiff y0 (hK hy0)
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun x : E => L z * Real.sqrt (2 * B * ‖x - y0‖)) :=
    continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.mul (continuous_id.sub continuous_const).norm))
  have hg : Tendsto (fun x : E => L z * Real.sqrt (2 * B * ‖x - y0‖)) (𝓝[K] y0) (𝓝 0) := by
    have := hc.tendsto y0
    simp only [sub_self, norm_zero, mul_zero, Real.sqrt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ x in 𝓝[K] y0, ‖f x z - f y0 z‖ ≤ L z * Real.sqrt (2 * B * ‖x - y0‖) := by
    filter_upwards [inter_mem_nhdsWithin K (Metric.ball_mem_nhds y0 hr)] with x hx
    obtain ⟨hxK, hxb⟩ := hx
    rw [Real.norm_eq_abs]
    refine (hlip x hxK y0 hy0 z).trans ?_
    apply mul_le_mul_of_nonneg_left _ (hL0 z)
    apply Real.sqrt_le_sqrt
    have hb1 := hB x hxb
    have hb2 := hB y0 (Metric.mem_ball_self hr)
    have hn := norm_nonneg (x - y0)
    have e1 : |fderiv ℝ Φ.val y0 (x - y0)| ≤ ‖fderiv ℝ Φ.val y0‖ * ‖x - y0‖ := by
      have := (fderiv ℝ Φ.val y0).le_opNorm (x - y0)
      rwa [Real.norm_eq_abs] at this
    have e2 : |fderiv ℝ Φ.val x (y0 - x)| ≤ ‖fderiv ℝ Φ.val x‖ * ‖x - y0‖ := by
      have := (fderiv ℝ Φ.val x).le_opNorm (y0 - x)
      rwa [Real.norm_eq_abs, norm_sub_rev y0 x] at this
    unfold bregmanSym bregman
    nlinarith [neg_le_abs (fderiv ℝ Φ.val y0 (x - y0)), neg_le_abs (fderiv ℝ Φ.val x (y0 - x)),
      mul_le_mul_of_nonneg_right hb1 hn, mul_le_mul_of_nonneg_right hb2 hn]
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hg

end S_H_cont

section S_I_pop
set_option autoImplicit false

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pop_weaklyConvex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (ρ : ℝ) (hint : ∀ x, Integrable (f x) P)
    (hconv : ∀ᵐ z ∂P, WeaklyConvexRel Φ (sampleFn r f z) ρ) :
    WeaklyConvexRel Φ (popRisk P r f) ρ := by
  obtain ⟨z0, hz0⟩ := hconv.exists
  refine ⟨hz0.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have key : ∀ᵐ z ∂P, f (a • x + b • y) z + (r.val (a • x + b • y) + ρ * Φ.val (a • x + b • y))
      ≤ a * f x z + b * f y z + (a * (r.val x + ρ * Φ.val x) + b * (r.val y + ρ * Φ.val y)) := by
    filter_upwards [hconv] with z hz
    have := hz.2 hx hy ha hb hab
    simp only [sampleFn, smul_eq_mul] at this
    linarith
  have hI1 : Integrable (fun z => f (a • x + b • y) z
      + (r.val (a • x + b • y) + ρ * Φ.val (a • x + b • y))) P := (hint _).add (integrable_const _)
  have hI2 : Integrable (fun z => a * f x z + b * f y z
      + (a * (r.val x + ρ * Φ.val x) + b * (r.val y + ρ * Φ.val y))) P :=
    (((hint x).const_mul a).add ((hint y).const_mul b)).add (integrable_const _)
  have hm := integral_mono_ae hI1 hI2 key
  have e1 : ∫ z, (f (a • x + b • y) z + (r.val (a • x + b • y) + ρ * Φ.val (a • x + b • y))) ∂P
      = (∫ z, f (a • x + b • y) z ∂P) + (r.val (a • x + b • y) + ρ * Φ.val (a • x + b • y)) := by
    rw [integral_add (hint _) (integrable_const _)]; simp
  have e2 : ∫ z, (a * f x z + b * f y z
      + (a * (r.val x + ρ * Φ.val x) + b * (r.val y + ρ * Φ.val y))) ∂P
      = a * (∫ z, f x z ∂P) + b * (∫ z, f y z ∂P)
        + (a * (r.val x + ρ * Φ.val x) + b * (r.val y + ρ * Φ.val y)) := by
    have ha' : Integrable (fun z => a * f x z) P := (hint x).const_mul a
    have hb' : Integrable (fun z => b * f y z) P := (hint y).const_mul b
    have hab' : Integrable (fun z => a * f x z + b * f y z) P := ha'.add hb'
    rw [integral_add hab' (integrable_const _), integral_add ha' hb', integral_const_mul,
      integral_const_mul]
    simp
  rw [e1, e2] at hm
  show (∫ z, f (a • x + b • y) z ∂P) + r.val (a • x + b • y) + ρ * Φ.val (a • x + b • y)
    ≤ a • ((∫ z, f x z ∂P) + r.val x + ρ * Φ.val x) + b • ((∫ z, f y z ∂P) + r.val y + ρ * Φ.val y)
  simp only [smul_eq_mul]
  linarith

end S_I_pop

section S_D_bdd
set_option autoImplicit false

open MeasureTheory Real Filter

end S_D_bdd


section S_N_point
set_option autoImplicit false

open MeasureTheory Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bsym_comm_N (Φ : ExtFn E) (x y : E) : bregmanSym Φ x y = bregmanSym Φ y x := by
  unfold bregmanSym; ring

-- Per-net-point tail (N_point, s7): fixed centre t, population prox xb, measurable selector xsel.
set_option maxHeartbeats 1000000 in
theorem point_tail_t [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ α σ : ℝ)
    (hA : Assumptions P Φ r f L ρ α σ) (s lam : ℝ) (hs : 0 ≤ s)
    (hlam : Integrable (fun z => Real.cosh (lam * L z)) P)
    (m : ℕ) (hm : 0 < m) (rhoBar : ℝ) (hρ : ρ < rhoBar)
    (u0 : E) (hu0 : u0 ∈ r.dom) (hu0i : u0 ∈ interior Φ.dom)
    (G0 : Set Ω) (hG0m : MeasurableSet G0) (hG0n : P G0ᶜ = 0) (z0 : Ω) (hz0 : z0 ∈ G0)
    (hwS : ∀ S : Fin m → Ω, (∀ i, S i ∈ G0) → WeaklyConvexRel Φ (empRisk r f S) ρ)
    (hwP : WeaklyConvexRel Φ (popRisk P r f) ρ)
    (t xb : E) (hb : xb ∈ proxSet Φ (popRisk P r f) rhoBar t) (hbi : xb ∈ interior Φ.dom)
    (xsel : (Fin m → Ω) → E) (hxm : Measurable xsel)
    (hsel : ∀ S, (∀ i, S i ∈ G0) → xsel S ∈ proxSet Φ (empRisk r f S) rhoBar t)
    (hseli : ∀ S, (∀ i, S i ∈ G0) → xsel S ∈ interior Φ.dom) :
    (Measure.pi fun _ : Fin m => P)
        {S | Real.sqrt (4 * (σ + s) ^ 2 / (α * (rhoBar - ρ) ^ 2 * m))
          < ‖xsel (projG G0 z0 ∘ S) - xb‖}
      ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * (lam * (s / Real.sqrt m)
          - Real.log (∫ z, Real.cosh (lam * L z) ∂P))))) := by
  have hα := hA.alpha_pos
  have hgap : 0 < rhoBar - ρ := sub_pos.2 hρ
  have hdiff := hA.legendre.differentiableOn
  have hae : ∀ᵐ z ∂P, z ∈ G0 := MeasureTheory.mem_ae_iff.2 hG0n
  have hLt : ∀ᵐ z ∂P, L (projG G0 z0 z) = L z := hae.mono fun z hz => by
    rw [projG_of_mem G0 z0 z hz]
  have hL2 : ∫ z, (L ∘ projG G0 z0) z ^ 2 ∂P = ∫ z, L z ^ 2 ∂P :=
    integral_congr_ae (hLt.mono fun z hz => by simp only [Function.comp_apply, hz])
  have hcosh : ∫ z, Real.cosh (lam * (L ∘ projG G0 z0) z) ∂P = ∫ z, Real.cosh (lam * L z) ∂P :=
    integral_congr_ae (hLt.mono fun z hz => by simp only [Function.comp_apply, hz])
  have hint' : Integrable (fun z => Real.cosh (lam * (L ∘ projG G0 z0) z)) P :=
    hlam.congr (hLt.mono fun z hz => by simp only [Function.comp_apply, hz])
  have hgood : ∀ S : Fin m → Ω, ∀ i, (projG G0 z0 ∘ S) i ∈ G0 :=
    fun S i => projG_mem G0 z0 hz0 (S i)
  have hxr : ∀ S : Fin m → Ω, xsel (projG G0 z0 ∘ S) ∈ r.dom := fun S => (hsel _ (hgood S)).1.1
  have hxi : ∀ S : Fin m → Ω, xsel (projG G0 z0 ∘ S) ∈ interior Φ.dom :=
    fun S => hseli _ (hgood S)
  have hxK : ∀ S : Fin m → Ω, xsel (projG G0 z0 ∘ S) ∈ interior Φ.dom ∩ r.dom :=
    fun S => ⟨hxi S, hxr S⟩
  have hbr : xb ∈ r.dom := hb.1.1
  have hbK : xb ∈ interior Φ.dom ∩ r.dom := ⟨hbi, hbr⟩
  have hpm : Measurable (fun S : Fin m → Ω => projG G0 z0 ∘ S) :=
    measurable_pi_lambda _ fun i => (projG_measurable G0 hG0m z0).comp (measurable_pi_apply i)
  have hxm' : Measurable (fun S : Fin m → Ω => xsel (projG G0 z0 ∘ S)) := hxm.comp hpm
  have hGm : Measurable (fun S : Fin m → Ω => ‖xsel (projG G0 z0 ∘ S) - xb‖) :=
    (hxm'.sub_const xb).norm
  have hd : ∀ (S : Fin m → Ω) (i : Fin m) (z : Ω),
      |‖xsel (projG G0 z0 ∘ S) - xb‖ - ‖xsel (projG G0 z0 ∘ Function.update S i z) - xb‖|
        ≤ 1 / (Real.sqrt α * m * (rhoBar - ρ))
          * ((L ∘ projG G0 z0) (S i) + (L ∘ projG G0 z0) z) :=
    fun S i z => point_hd hm Φ r f L ρ rhoBar α hα hρ hA.legendre hA.strongConvex hA.lipschitz
      hA.L_nonneg u0 hu0 hu0i G0 z0 hz0 hwS t xb xsel hsel S i z
  have hD2le : ∀ S : Fin m → Ω, α * ‖xsel (projG G0 z0 ∘ S) - xb‖ ^ 2
      ≤ bregmanSym Φ xb (xsel (projG G0 z0 ∘ S)) := by
    intro S
    have h1 := hA.strongConvex xb ⟨hbr, hbi⟩ _ ⟨hxr S, hxi S⟩
    have h2 := hA.strongConvex _ ⟨hxr S, hxi S⟩ xb ⟨hbr, hbi⟩
    rw [norm_sub_rev] at h2
    unfold bregmanSym; linarith
  have hF : Measurable (Function.uncurry
      fun (S : Fin m → Ω) (z : Ω) => f (xsel (projG G0 z0 ∘ S)) z) :=
    carath_meas (interior Φ.dom ∩ r.dom) f
      (fun z => f_contOn Φ _ Set.inter_subset_left hA.legendre.strictConvex.convexOn hdiff f L
        hA.L_nonneg (fun x hx y hy z => hA.lipschitz x hx y hy z) z)
      hA.f_measurable _ hxm' hxK
  have hgoodae : ∀ᵐ S ∂(Measure.pi fun _ : Fin m => P), ∀ i, S i ∈ G0 :=
    MeasureTheory.mem_ae_iff.2 (good_null P m G0 hG0n)
  have H1 : ∀ᵐ S ∂(Measure.pi fun _ : Fin m => P),
      (rhoBar - ρ) * bregmanSym Φ xb (xsel (projG G0 z0 ∘ S))
        ≤ (1 / (m : ℝ)) * ∑ i, (f xb (S i) - f (xsel (projG G0 z0 ∘ S)) (S i))
          - ∫ z, (f xb z - f (xsel (projG G0 z0 ∘ S)) z) ∂P := by
    filter_upwards [hgoodae] with S hS
    have hpS : projG G0 z0 ∘ S = S := funext fun i => projG_of_mem G0 z0 (S i) (hS i)
    rw [hpS, bsym_comm_N]
    exact H1_step P Φ r f ρ rhoBar hA.f_integrable S t _ xb (hwS S hS) hwP (hsel S hS) hb
      ((hdiff _ (hseli S hS)).differentiableAt (isOpen_interior.mem_nhds (hseli S hS)))
      ((hdiff _ hbi).differentiableAt (isOpen_interior.mem_nhds hbi))
  have hsc0 : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom,
      0 ≤ bregmanSym Φ x y := by
    intro x hx y hy
    have h1 := hA.strongConvex x hx y hy
    have h2 := hA.strongConvex y hy x hx
    unfold bregmanSym
    nlinarith [mul_nonneg hα.le (sq_nonneg ‖y - x‖), mul_nonneg hα.le (sq_nonneg ‖x - y‖)]
  have Hstab : ∀ i : Fin m, ∀ᵐ p ∂((Measure.pi fun _ : Fin m => P).prod P),
      f (xsel (projG G0 z0 ∘ Function.update p.1 i p.2)) (p.1 i)
          - f (xsel (projG G0 z0 ∘ p.1)) (p.1 i)
        ≤ L (p.1 i) * (L (p.1 i) + L p.2) / (m * (rhoBar - ρ)) := by
    intro i
    have h1 : ∀ᵐ p ∂((Measure.pi fun _ : Fin m => P).prod P), ∀ j, p.1 j ∈ G0 :=
      Measure.quasiMeasurePreserving_fst.ae hgoodae
    have h2 : ∀ᵐ p ∂((Measure.pi fun _ : Fin m => P).prod P), p.2 ∈ G0 :=
      Measure.quasiMeasurePreserving_snd.ae hae
    filter_upwards [h1, h2] with p hp1 hp2
    have hgu : ∀ j, Function.update p.1 i p.2 j ∈ G0 := by
      intro j; rw [Function.update_apply]; split_ifs
      · exact hp2
      · exact hp1 j
    have e1 : projG G0 z0 ∘ p.1 = p.1 := funext fun j => projG_of_mem G0 z0 _ (hp1 j)
    have e2 : projG G0 z0 ∘ Function.update p.1 i p.2 = Function.update p.1 i p.2 :=
      funext fun j => projG_of_mem G0 z0 _ (hgu j)
    rw [e1, e2]
    exact stab_step hm Φ r f L ρ rhoBar hρ hsc0 hA.lipschitz hA.L_nonneg p.1 i p.2 t _ _
      (hwS _ hp1) (hwS _ hgu) (hsel _ hp1) (hsel _ hgu) (hseli _ hp1) (hseli _ hgu) hdiff
  obtain ⟨hDi, hEB⟩ := bias_bound P m hm L hA.L_nonneg hA.L_memLp (fun z => f xb z)
    (hA.f_measurable xb) (fun S z => f (xsel (projG G0 z0 ∘ S)) z) hF
    (fun S => bregmanSym Φ xb (xsel (projG G0 z0 ∘ S)))
    (fun S => le_trans (mul_nonneg hα.le (sq_nonneg _)) (hD2le S))
    (fun S => α * ‖xsel (projG G0 z0 ∘ S) - xb‖ ^ 2)
    ((measurable_const.mul (hGm.pow_const 2)).aestronglyMeasurable)
    (fun S => mul_nonneg hα.le (sq_nonneg _)) hD2le (rhoBar - ρ) hgap
    (fun S z => hA.lipschitz xb hbK _ (hxK S) z) H1 Hstab
  have hEB2 : (rhoBar - ρ) * ∫ S, α * ‖xsel (projG G0 z0 ∘ S) - xb‖ ^ 2
      ∂(Measure.pi fun _ : Fin m => P) ≤ 2 * (∫ z, L z ^ 2 ∂P) / (m * (rhoBar - ρ)) := hEB
  have hEB' : ∫ S, α * ‖xsel (projG G0 z0 ∘ S) - xb‖ ^ 2 ∂(Measure.pi fun _ : Fin m => P)
      ≤ 2 * (∫ z, (L ∘ projG G0 z0) z ^ 2 ∂P) / (m * (rhoBar - ρ) ^ 2) := by
    rw [hL2]
    rw [show ((m : ℝ) * (rhoBar - ρ) ^ 2) = ((m : ℝ) * (rhoBar - ρ)) * (rhoBar - ρ) by ring,
      ← div_div]
    rw [le_div_iff₀ hgap]; linarith [hEB2]
  have key := point_tail_all P (L ∘ projG G0 z0) σ s lam α (rhoBar - ρ)
    (by rw [hL2]; exact hA.sigma_bound) hs hint' hα hgap m hm
    (fun S => ‖xsel (projG G0 z0 ∘ S) - xb‖) hGm (fun S => norm_nonneg _) hd hDi hEB'
  refine le_trans key (le_of_eq ?_)
  rw [hcosh]

end S_N_point

section S_O_sel
set_option autoImplicit false

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Measurable prox selector on good samples (O_sel, s7): unique minimizer by quadratic growth.
set_option maxHeartbeats 1000000 in
theorem sel_exists [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ)
    (ρ α rhoBar : ℝ) (hL : IsLegendre Φ) (hα : 0 < α) (hρ : ρ < rhoBar) (hrb : 0 < rhoBar)
    (hsc : ∀ x ∈ r.dom ∩ interior Φ.dom, ∀ y ∈ r.dom ∩ interior Φ.dom,
      α / 2 * ‖y - x‖ ^ 2 ≤ bregman Φ x y)
    (hlip : ∀ x ∈ interior Φ.dom ∩ r.dom, ∀ y ∈ interior Φ.dom ∩ r.dom, ∀ z,
      |f x z - f y z| ≤ L z * Real.sqrt (bregmanSym Φ x y))
    (hL0 : ∀ z, 0 ≤ L z) (hfm : ∀ x, Measurable (f x)) (hrc : Convex ℝ r.dom)
    (u0 : E) (hu0 : u0 ∈ r.dom) (hu0i : u0 ∈ interior Φ.dom)
    (m : ℕ) (G0 : Set Ω) (hG0m : MeasurableSet G0)
    (hgS : ∀ S : Fin m → Ω, (∀ i, S i ∈ G0) → (empRisk r f S).IsClosed ∧
      WeaklyConvexRel Φ (empRisk r f S) ρ ∧ ∃ b, ∀ u ∈ r.dom, b ≤ (empRisk r f S).val u)
    (t : E) :
    ∃ xsel : (Fin m → Ω) → E, Measurable xsel ∧
      ∀ S, (∀ i, S i ∈ G0) → xsel S ∈ proxSet Φ (empRisk r f S) rhoBar t ∧
        xsel S ∈ interior Φ.dom := by
  classical
  have hex : ∀ S : Fin m → Ω, (∀ i, S i ∈ G0) →
      (proxSet Φ (empRisk r f S) rhoBar t).Nonempty := by
    intro S hS
    obtain ⟨hc, -, b, hb⟩ := hgS S hS
    exact prox_exists Φ (empRisk r f S) α rhoBar b u0 t hL.closed hL.strictConvex.convexOn hc
      hrc hb hu0 hu0i hα hrb (fun x hx => hsc x hx u0 ⟨hu0, hu0i⟩)
  have hGm : MeasurableSet {S : Fin m → Ω | ∀ i, S i ∈ G0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurable_pi_apply i hG0m
  let xsel : (Fin m → Ω) → E := fun S => if h : (∀ i, S i ∈ G0) then (hex S h).some else u0
  have hxs : ∀ S (h : ∀ i, S i ∈ G0), xsel S = (hex S h).some := fun S h => dif_pos h
  have hxn : ∀ S, ¬ (∀ i, S i ∈ G0) → xsel S = u0 := fun S h => dif_neg h
  have hprop : ∀ S, (∀ i, S i ∈ G0) → xsel S ∈ proxSet Φ (empRisk r f S) rhoBar t ∧
      xsel S ∈ interior Φ.dom := by
    intro S hS
    rw [hxs S hS]
    exact ⟨(hex S hS).some_mem, prox_interior Φ _ ρ rhoBar t _ u0 hL (hgS S hS).2.1 hρ
      (hex S hS).some_mem hu0 hu0i⟩
  refine ⟨xsel, ?_, hprop⟩
  apply measurable_of_norm_sub
  intro q
  have hK : ∀ S ∈ {S : Fin m → Ω | ∀ i, S i ∈ G0}, xsel S ∈ interior Φ.dom ∩ r.dom :=
    fun S hS => ⟨(hprop S hS).2, (hprop S hS).1.1.1⟩
  have hcont : ∀ S : Fin m → Ω,
      ContinuousOn (fun u => (1 / (m : ℝ)) * ∑ i, f u (S i)) (interior Φ.dom ∩ r.dom) :=
    fun S => continuousOn_const.mul (continuousOn_finset_sum _ fun i _ =>
      f_contOn Φ _ Set.inter_subset_left hL.strictConvex.convexOn hL.differentiableOn f L hL0
        hlip (S i))
  have hmeas : ∀ u : E, Measurable (fun S : Fin m → Ω => (1 / (m : ℝ)) * ∑ i, f u (S i)) :=
    fun u => measurable_const.mul
      (Finset.measurable_sum _ fun i _ => (hfm u).comp (measurable_pi_apply i))
  have hgrow : ∀ S ∈ {S : Fin m → Ω | ∀ i, S i ∈ G0}, ∀ u ∈ interior Φ.dom ∩ r.dom,
      (1 / (m : ℝ)) * ∑ i, f (xsel S) (S i) + (r.val (xsel S) + rhoBar * bregman Φ (xsel S) t)
        + (rhoBar - ρ) * (α / 2) * ‖u - xsel S‖ ^ 2
        ≤ (1 / (m : ℝ)) * ∑ i, f u (S i) + (r.val u + rhoBar * bregman Φ u t) := by
    intro S hS u hu
    have hpS := (hprop S hS).1
    have hpi := (hprop S hS).2
    have h3 := three_point Φ (empRisk r f S) ρ rhoBar t (xsel S) u (hgS S hS).2.1 hpS
      ((hL.differentiableOn _ hpi).differentiableAt (isOpen_interior.mem_nhds hpi))
      ⟨hu.2, interior_subset hu.1⟩
    have h4 := hsc u ⟨hu.2, hu.1⟩ (xsel S) ⟨hpS.1.1, hpi⟩
    rw [norm_sub_rev] at h4
    have h3' : (1 / (m : ℝ)) * ∑ i, f (xsel S) (S i) + r.val (xsel S)
        + rhoBar * bregman Φ (xsel S) t + (rhoBar - ρ) * bregman Φ u (xsel S)
        ≤ (1 / (m : ℝ)) * ∑ i, f u (S i) + r.val u + rhoBar * bregman Φ u t := h3
    have hg : 0 ≤ rhoBar - ρ := (sub_pos.2 hρ).le
    nlinarith [mul_le_mul_of_nonneg_left h4 hg]
  have h1 := meas_dist_of_growth (interior Φ.dom ∩ r.dom)
    (fun (S : Fin m → Ω) u => (1 / (m : ℝ)) * ∑ i, f u (S i))
    (fun u => r.val u + rhoBar * bregman Φ u t) ((rhoBar - ρ) * (α / 2))
    (mul_pos (sub_pos.2 hρ) (half_pos hα)) hcont hmeas _ hGm xsel hK hgrow q
  have h2 : Measurable ({S : Fin m → Ω | ∀ i, S i ∈ G0}ᶜ.indicator
      (fun _ : Fin m → Ω => ‖u0 - q‖)) :=
    measurable_const.indicator hGm.compl
  convert h1.add h2 using 1
  funext S
  simp only [Pi.add_apply, Set.indicator_apply, Set.mem_compl_iff]
  by_cases hS : S ∈ {S : Fin m → Ω | ∀ i, S i ∈ G0}
  · rw [if_pos hS, if_neg (not_not.2 hS), add_zero]
  · rw [if_neg hS, if_pos hS, zero_add, hxn S hS]

end S_O_sel

section S_P_part1
set_option autoImplicit false

open MeasureTheory Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Part 1 of theorem 4.4 (P_part1, s7): union bound over the net.
set_option maxHeartbeats 1000000 in
theorem part1 [FiniteDimensional ℝ E] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ α σ : ℝ)
    (hA : Assumptions P Φ r f L ρ α σ) (C : Set E) (δ s : ℝ) (hs : 0 ≤ s)
    (m : ℕ) (hm : 0 < m) (T : Finset E)
    (hnet : ∀ y ∈ C, ∃ t ∈ T, ‖fderiv ℝ Φ.val y - fderiv ℝ Φ.val t‖ ≤ δ)
    (lam : ℝ) (hlam : Integrable (fun z => Real.cosh (lam * L z)) P) :
    ∀ rhoBar : ℝ, 0 < rhoBar → ρ < rhoBar →
      (Measure.pi fun _ : Fin m => P)
          {S | ∃ y ∈ C, ∃ a ∈ proxSet Φ (empRisk r f S) rhoBar y,
            ∃ b ∈ proxSet Φ (popRisk P r f) rhoBar y,
              Real.sqrt (4 * (σ + s) ^ 2 / (α * (rhoBar - ρ) ^ 2 * m))
                + 2 * rhoBar * δ / (α * (rhoBar - ρ)) < ‖a - b‖}
        ≤ (T.card : ENNReal) *
            ENNReal.ofReal (Real.exp (-((m : ℝ) * (lam * (s / Real.sqrt m)
              - logMGFSym P L lam)))) := by
  intro rhoBar hrb hρ
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hα := hA.alpha_pos
  obtain ⟨u0, hu0, hu0i⟩ := base_point Φ r hA.compatible hA.r_dom_convex hA.r_proper
  obtain ⟨G0, hG0ae, hG0m, hG0good⟩ := hA.goodSample.exists_measurable_mem
  have hG0n : P G0ᶜ = 0 := MeasureTheory.mem_ae_iff.1 hG0ae
  obtain ⟨z0, hz0⟩ : G0.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    subst h
    simp at hG0n
  have hgS : ∀ S : Fin m → Ω, (∀ i, S i ∈ G0) → (empRisk r f S).IsClosed ∧
      WeaklyConvexRel Φ (empRisk r f S) ρ ∧ ∃ b, ∀ u ∈ r.dom, b ≤ (empRisk r f S).val u :=
    fun S hS => ⟨empRisk_closed hm r f S fun i => (hG0good _ (hS i)).closed,
      empRisk_weaklyConvex hm Φ r f ρ S fun i => (hG0good _ (hS i)).weaklyConvex,
      empRisk_lb hm r f S fun i => (hG0good _ (hS i)).bddBelow⟩
  have hwP : WeaklyConvexRel Φ (popRisk P r f) ρ :=
    pop_weaklyConvex P Φ r f ρ hA.f_integrable (hA.goodSample.mono fun z hz => hz.weaklyConvex)
  choose xsel hxm hxp using fun t : E => sel_exists Φ r f L ρ α rhoBar hA.legendre hα hρ hrb
    hA.strongConvex hA.lipschitz hA.L_nonneg hA.f_measurable hA.r_dom_convex u0 hu0 hu0i m G0
    hG0m hgS t
  obtain ⟨bP, hbP⟩ := hA.pop_bddBelow
  have hxbex : ∀ t : E, (proxSet Φ (popRisk P r f) rhoBar t).Nonempty := fun t =>
    prox_exists Φ (popRisk P r f) α rhoBar bP u0 t hA.legendre.closed
      hA.legendre.strictConvex.convexOn hA.pop_closed hA.r_dom_convex
      (fun u hu => hbP ⟨u, hu, rfl⟩) hu0 hu0i hα hrb
      (fun x hx => hA.strongConvex x hx u0 ⟨hu0, hu0i⟩)
  choose xb hxb using hxbex
  have hxbi : ∀ t, xb t ∈ interior Φ.dom := fun t =>
    prox_interior Φ _ ρ rhoBar t _ u0 hA.legendre hwP hρ (hxb t) hu0 hu0i
  have hR := fun t => point_tail_t P Φ r f L ρ α σ hA s lam hs hlam m hm rhoBar hρ u0 hu0 hu0i
    G0 hG0m hG0n z0 hz0 (fun S hS => (hgS S hS).2.1) hwP t (xb t) (hxb t) (hxbi t) (xsel t)
    (hxm t) (fun S hS => (hxp t S hS).1) (fun S hS => (hxp t S hS).2)
  refine union_net (Measure.pi fun _ : Fin m => P) _ {S | ∀ i, S i ∈ G0}
    (good_null P m G0 hG0n) T (fun t S => ‖xsel t (projG G0 z0 ∘ S) - xb t‖)
    (Real.sqrt (4 * (σ + s) ^ 2 / (α * (rhoBar - ρ) ^ 2 * m))) _
    (fun t _ => hR t) ?_
  intro S hS hEv
  have hpS : projG G0 z0 ∘ S = S := funext fun i => projG_of_mem G0 z0 (S i) (hS i)
  show ∃ t ∈ T, Real.sqrt (4 * (σ + s) ^ 2 / (α * (rhoBar - ρ) ^ 2 * m))
    < ‖xsel t (projG G0 z0 ∘ S) - xb t‖
  rw [hpS]
  exact part1_cov P Φ r f ρ rhoBar α δ _ u0 hA.legendre hρ hrb.le hα hu0 hu0i hA.strongConvex
    C T hnet S ((hgS S hS).2.1) hwP (fun t => xsel t S) xb (fun t _ => (hxp t S hS).1)
    (fun t _ => hxb t) hEv

end S_P_part1

section S_Q_env
set_option autoImplicit false

open Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem env_eq (Φ g : ExtFn E) (rhoBar : ℝ) (x p : E) (hp : p ∈ proxSet Φ g rhoBar x) :
    envelope Φ g rhoBar x = g.val p + rhoBar * bregman Φ p x := by
  unfold envelope
  refine IsLeast.csInf_eq ⟨⟨p, hp.1, rfl⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hp.2 hu

theorem bregman_hasFDerivAt (Φ : ExtFn E) (p x : E) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hΦ : ∀ᶠ y in 𝓝 x, HasFDerivAt Φ.val (fderiv ℝ Φ.val y) y)
    (hH : HasFDerivAt (fderiv ℝ Φ.val) H x) :
    HasFDerivAt (fun x' => bregman Φ p x') (H (x - p)) x := by
  have hu : HasFDerivAt (fun x' : E => p - x') (-ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_sub p
  have h1 := hH.clm_apply hu
  have h2 := ((hasFDerivAt_const (Φ.val p) x).sub hΦ.self_of_nhds).sub h1
  refine h2.congr_fderiv ?_
  ext h
  have hsym := second_derivative_symmetric_of_eventually hΦ hH h (x - p)
  have hneg : (H h) (p - x) = -((H h) (x - p)) := by rw [← map_neg, neg_sub]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_neg, hneg, ← hsym]
  ring

-- Envelope gradient formula (Q_env, s7): ∇ e(x) = ρ̄ • H(x - p), H = ∇²Φ(x).
set_option maxHeartbeats 1000000 in
theorem env_hasFDerivAt (Φ g : ExtFn E) (ρ rhoBar α : ℝ) (hw : WeaklyConvexRel Φ g ρ)
    (hρ : ρ < rhoBar) (hrb : 0 ≤ rhoBar) (hα : 0 < α)
    (hsc : ∀ u ∈ g.dom ∩ interior Φ.dom, ∀ v ∈ g.dom ∩ interior Φ.dom,
      α / 2 * ‖v - u‖ ^ 2 ≤ bregman Φ u v)
    (hdiff : DifferentiableOn ℝ Φ.val (interior Φ.dom))
    (hex : ∀ y ∈ interior Φ.dom, ∃ q ∈ proxSet Φ g rhoBar y, q ∈ interior Φ.dom)
    (x p : E) (hx : x ∈ interior Φ.dom) (hp : p ∈ proxSet Φ g rhoBar x)
    (hpi : p ∈ interior Φ.dom)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hH : HasFDerivAt (fderiv ℝ Φ.val) H x) :
    HasFDerivAt (envelope Φ g rhoBar) (rhoBar • H (x - p)) x := by
  have hΦ : ∀ᶠ y in 𝓝 x, HasFDerivAt Φ.val (fderiv ℝ Φ.val y) y := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact ((hdiff y hy).differentiableAt (isOpen_interior.mem_nhds hy)).hasFDerivAt
  have hA := (bregman_hasFDerivAt Φ p x H hΦ hH).const_mul rhoBar
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hA ⊢
  have hT : Tendsto (fun h : E => x + h) (𝓝 0) (𝓝 x) := by
    simpa using ((continuous_const_add x).tendsto (0 : E))
  have hBO : (fun h : E => fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x) =O[𝓝 0]
      (fun h : E => h) := by
    have := hH.isBigO_sub.comp_tendsto hT
    simpa [Function.comp_def] using this
  have hTo : Tendsto (fun h : E => fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x) (𝓝 0) (𝓝 0) := by
    have := (hH.continuousAt.tendsto.comp hT).sub_const (fderiv ℝ Φ.val x)
    simpa [Function.comp_def] using this
  have hsq : (fun h : E => ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖
      * ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖) =o[𝓝 0] (fun h : E => h) := by
    have h1 := hBO.norm_norm
    have h2 := ((isLittleO_one_iff ℝ).2 hTo).norm_left
    have h3 := h1.mul_isLittleO h2
    simp only [mul_one] at h3
    exact h3.trans_isBigO (isBigO_refl (fun h : E => h) (𝓝 0)).norm_left
  have hgap : 0 < rhoBar - ρ := sub_pos.2 hρ
  have hE : ∀ᶠ h in 𝓝 (0:E), ‖rhoBar * bregman Φ p (x + h) - rhoBar * bregman Φ p x
      - (envelope Φ g rhoBar (x + h) - envelope Φ g rhoBar x)‖
      ≤ rhoBar ^ 2 / (α * (rhoBar - ρ)) * ‖‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖
        * ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖‖ := by
    have hev : ∀ᶠ h in 𝓝 (0:E), x + h ∈ interior Φ.dom := hT (isOpen_interior.mem_nhds hx)
    filter_upwards [hev] with h hh
    obtain ⟨q, hq, hqi⟩ := hex _ hh
    rw [env_eq Φ g rhoBar _ q hq, env_eq Φ g rhoBar _ p hp,
      Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hmin1 : g.val q + rhoBar * bregman Φ q (x + h)
        ≤ g.val p + rhoBar * bregman Φ p (x + h) := hq.2 hp.1
    have hmin2 : g.val p + rhoBar * bregman Φ p x ≤ g.val q + rhoBar * bregman Φ q x := hp.2 hq.1
    have hid : rhoBar * (bregman Φ q (x + h) - bregman Φ q x
        - (bregman Φ p (x + h) - bregman Φ p x))
        = -(rhoBar * ((fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x) (q - p))) := by
      unfold bregman; simp only [ContinuousLinearMap.sub_apply, map_sub]; ring
    have hlin : (fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x) (q - p)
        ≤ ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖ * ‖q - p‖ :=
      le_trans (le_abs_self _) (by
        rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
    have hdq := (hdiff q hqi).differentiableAt (isOpen_interior.mem_nhds hqi)
    have hdp := (hdiff p hpi).differentiableAt (isOpen_interior.mem_nhds hpi)
    have hqp : ‖q - p‖ ≤ rhoBar * ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖
        / (α * (rhoBar - ρ)) :=
      net_perturb Φ g ρ rhoBar α _ (x + h) x q p hw hq hp hdq hdp
        (hsc q ⟨hq.1.1, hqi⟩ p ⟨hp.1.1, hpi⟩) (hsc p ⟨hp.1.1, hpi⟩ q ⟨hq.1.1, hqi⟩)
        hα hρ hrb le_rfl
    have hM := mul_le_mul_of_nonneg_left hqp (norm_nonneg
      (fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x))
    have hR := mul_le_mul_of_nonneg_left (le_trans hlin hM) hrb
    have heq : rhoBar * (‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖
        * (rhoBar * ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖ / (α * (rhoBar - ρ))))
        = rhoBar ^ 2 / (α * (rhoBar - ρ)) * (‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖
          * ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    have hB0 : 0 ≤ rhoBar ^ 2 / (α * (rhoBar - ρ)) * (‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖
          * ‖fderiv ℝ Φ.val (x + h) - fderiv ℝ Φ.val x‖) :=
      mul_nonneg (div_nonneg (sq_nonneg _) (mul_pos hα hgap).le)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith
    · linarith
  have hEo : (fun h : E => rhoBar * bregman Φ p (x + h) - rhoBar * bregman Φ p x
      - (envelope Φ g rhoBar (x + h) - envelope Φ g rhoBar x)) =o[𝓝 0] (fun h : E => h) :=
    (IsBigO.of_bound _ hE).trans_isLittleO hsq
  refine (hA.sub hEo).congr_left fun h => ?_
  beta_reduce
  ring

end S_Q_env

section S_R_part2
set_option autoImplicit false

open MeasureTheory Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mono_null {X : Type*} [MeasurableSpace X] (μ : Measure X) (A B N : Set X) (R : ENNReal)
    (hN : μ Nᶜ = 0) (hAB : ∀ x ∈ N, x ∈ A → x ∈ B) (hB : μ B ≤ R) : μ A ≤ R := by
  calc μ A ≤ μ (B ∪ Nᶜ) := measure_mono fun x hx => by
        by_cases h : x ∈ N
        · exact Or.inl (hAB x h hx)
        · exact Or.inr h
    _ ≤ μ B + μ Nᶜ := measure_union_le _ _
    _ = μ B := by rw [hN, add_zero]
    _ ≤ R := hB

theorem prox_ex_int [FiniteDimensional ℝ E] (Φ g : ExtFn E) (ρ α rhoBar b : ℝ) (u0 : E)
    (hL : IsLegendre Φ) (hgc : g.IsClosed) (hgd : Convex ℝ g.dom) (hgb : ∀ u ∈ g.dom, b ≤ g.val u)
    (hw : WeaklyConvexRel Φ g ρ) (hu0 : u0 ∈ g.dom) (hu0i : u0 ∈ interior Φ.dom) (hα : 0 < α)
    (hρ : ρ < rhoBar) (hrb : 0 < rhoBar)
    (hsc : ∀ x ∈ g.dom ∩ interior Φ.dom, α / 2 * ‖u0 - x‖ ^ 2 ≤ bregman Φ x u0) (y : E) :
    ∃ q ∈ proxSet Φ g rhoBar y, q ∈ interior Φ.dom := by
  obtain ⟨q, hq⟩ := prox_exists Φ g α rhoBar b u0 y hL.closed hL.strictConvex.convexOn hgc hgd
    hgb hu0 hu0i hα hrb hsc
  exact ⟨q, hq, prox_interior Φ g ρ rhoBar y q u0 hL hw hρ hq hu0 hu0i⟩

theorem env_fderiv_of [FiniteDimensional ℝ E] (Φ g : ExtFn E) (ρ α rhoBar b : ℝ) (u0 : E)
    (hL : IsLegendre Φ) (hgc : g.IsClosed) (hgd : Convex ℝ g.dom) (hgb : ∀ u ∈ g.dom, b ≤ g.val u)
    (hw : WeaklyConvexRel Φ g ρ) (hu0 : u0 ∈ g.dom) (hu0i : u0 ∈ interior Φ.dom) (hα : 0 < α)
    (hρ : ρ < rhoBar) (hrb : 0 < rhoBar)
    (hsc2 : ∀ u ∈ g.dom ∩ interior Φ.dom, ∀ v ∈ g.dom ∩ interior Φ.dom,
      α / 2 * ‖v - u‖ ^ 2 ≤ bregman Φ u v)
    (hd2 : DifferentiableOn ℝ (fderiv ℝ Φ.val) (interior Φ.dom)) (y : E) (hy : y ∈ interior Φ.dom) :
    ∃ q ∈ proxSet Φ g rhoBar y,
      fderiv ℝ (envelope Φ g rhoBar) y = rhoBar • fderiv ℝ (fderiv ℝ Φ.val) y (y - q) := by
  have hex : ∀ y' ∈ interior Φ.dom, ∃ q ∈ proxSet Φ g rhoBar y', q ∈ interior Φ.dom :=
    fun y' _ => prox_ex_int Φ g ρ α rhoBar b u0 hL hgc hgd hgb hw hu0 hu0i hα hρ hrb
      (fun x hx => hsc2 x hx u0 ⟨hu0, hu0i⟩) y'
  obtain ⟨q, hq, hqi⟩ := hex y hy
  exact ⟨q, hq, (env_hasFDerivAt Φ g ρ rhoBar α hw hρ hrb.le hα hsc2 hL.differentiableOn hex y q
    hy hq hqi _ ((hd2 y hy).differentiableAt (isOpen_interior.mem_nhds hy)).hasFDerivAt).fderiv⟩

-- Part 2 of theorem 4.4 (R_part2, s7): envelope gradients reduce to part 1 at rhoBar = 2ρ.
set_option maxHeartbeats 1000000 in
theorem part2 [FiniteDimensional ℝ E] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ α σ : ℝ)
    (hA : Assumptions P Φ r f L ρ α σ) (C : Set E) (hC : C ⊆ interior Φ.dom) (δ s : ℝ)
    (hs : 0 ≤ s) (m : ℕ) (hm : 0 < m) (T : Finset E)
    (hnet : ∀ y ∈ C, ∃ t ∈ T, ‖fderiv ℝ Φ.val y - fderiv ℝ Φ.val t‖ ≤ δ)
    (lam : ℝ) (hlam : Integrable (fun z => Real.cosh (lam * L z)) P) :
    (0 < ρ → DifferentiableOn ℝ (fderiv ℝ Φ.val) (interior Φ.dom) →
      (∀ y ∈ C, HessInvertible Φ y) →
      (Measure.pi fun _ : Fin m => P)
          {S | ∃ y ∈ C, Real.sqrt (16 * (σ + s) ^ 2 / (α * m)) + 8 * ρ * δ / α <
            localDualNorm Φ y (fderiv ℝ (envelope Φ (empRisk r f S) (2 * ρ)) y
              - fderiv ℝ (envelope Φ (popRisk P r f) (2 * ρ)) y)}
        ≤ (T.card : ENNReal) *
            ENNReal.ofReal (Real.exp (-((m : ℝ) * (lam * (s / Real.sqrt m)
              - logMGFSym P L lam))))) := by
  intro hρ hd2 hHess
  have hα := hA.alpha_pos
  have h1 := part1 P Φ r f L ρ α σ hA C δ s hs m hm T hnet lam hlam (2 * ρ) (by linarith)
    (by linarith)
  obtain ⟨u0, hu0, hu0i⟩ := base_point Φ r hA.compatible hA.r_dom_convex hA.r_proper
  obtain ⟨G0, hG0ae, -, hG0good⟩ := hA.goodSample.exists_measurable_mem
  have hG0n : P G0ᶜ = 0 := MeasureTheory.mem_ae_iff.1 hG0ae
  have hwP : WeaklyConvexRel Φ (popRisk P r f) ρ :=
    pop_weaklyConvex P Φ r f ρ hA.f_integrable (hA.goodSample.mono fun z hz => hz.weaklyConvex)
  obtain ⟨bP, hbP⟩ := hA.pop_bddBelow
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have e1 : (2 * ρ - ρ) = ρ := by ring
  have hsq : (2 * ρ) ^ 2 * (4 * (σ + s) ^ 2 / (α * ρ ^ 2 * m)) = 16 * (σ + s) ^ 2 / (α * m) := by
    field_simp <;> ring
  have key : 2 * ρ * (Real.sqrt (4 * (σ + s) ^ 2 / (α * (2 * ρ - ρ) ^ 2 * m))
      + 2 * (2 * ρ) * δ / (α * (2 * ρ - ρ)))
      = Real.sqrt (16 * (σ + s) ^ 2 / (α * m)) + 8 * ρ * δ / α := by
    rw [e1, mul_add]
    congr 1
    · rw [← hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]
    · field_simp <;> ring
  refine mono_null _ _ _ {S : Fin m → Ω | ∀ i, S i ∈ G0} _ (good_null P m G0 hG0n) ?_ h1
  rintro S hS ⟨y, hyC, hlt⟩
  have hy := hC hyC
  obtain ⟨bS, hbS⟩ := empRisk_lb hm r f S fun i => (hG0good _ (hS i)).bddBelow
  obtain ⟨a, ha, hDa⟩ := env_fderiv_of Φ (empRisk r f S) ρ α (2 * ρ) bS u0 hA.legendre
    (empRisk_closed hm r f S fun i => (hG0good _ (hS i)).closed) hA.r_dom_convex hbS
    (empRisk_weaklyConvex hm Φ r f ρ S fun i => (hG0good _ (hS i)).weaklyConvex) hu0 hu0i hα
    (by linarith) (by linarith) hA.strongConvex hd2 y hy
  obtain ⟨b, hb, hDb⟩ := env_fderiv_of Φ (popRisk P r f) ρ α (2 * ρ) bP u0 hA.legendre
    hA.pop_closed hA.r_dom_convex (fun u hu => hbP ⟨u, hu, rfl⟩) hwP hu0 hu0i hα
    (by linarith) (by linarith) hA.strongConvex hd2 y hy
  have hinv : ∀ v : E,
      (fderiv ℝ (fderiv ℝ Φ.val) y).inverse (fderiv ℝ (fderiv ℝ Φ.val) y v) = v := by
    obtain ⟨e, he⟩ := hHess y hyC
    intro v
    rw [← he, ContinuousLinearMap.inverse_equiv]
    simp
  rw [hDa, hDb, ← smul_sub, ← map_sub, sub_sub_sub_cancel_left] at hlt
  unfold localDualNorm at hlt
  rw [map_smul, hinv, norm_smul, Real.norm_of_nonneg (by linarith), norm_sub_rev] at hlt
  refine ⟨y, hyC, a, ha, b, hb, ?_⟩
  refine lt_of_mul_lt_mul_left ?_ (by linarith : (0 : ℝ) ≤ 2 * ρ)
  rw [key]
  exact hlt

end S_R_part2

end GraphConvSubgrad.StatConc.Lib

open GraphConvSubgrad.StatConc MeasureTheory in
theorem solution {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ r : ExtFn E) (f : E → Ω → ℝ) (L : Ω → ℝ) (ρ α σ : ℝ)
    (hA : Assumptions P Φ r f L ρ α σ)
    (C : Set E) (hC : C ⊆ interior Φ.dom) (δ s : ℝ) (hδ : 0 < δ) (hs : 0 ≤ s)
    (m : ℕ) (hm : 0 < m)
    (T : Finset E) (hT : (T : Set E) ⊆ interior Φ.dom)
    (hnet : ∀ y ∈ C, ∃ t ∈ T, ‖fderiv ℝ Φ.val y - fderiv ℝ Φ.val t‖ ≤ δ)
    (lam : ℝ) (hlam : Integrable (fun z => Real.cosh (lam * L z)) P) :
    (∀ rhoBar : ℝ, 0 < rhoBar → ρ < rhoBar →
      (Measure.pi fun _ : Fin m => P)
          {S | ∃ y ∈ C, ∃ a ∈ proxSet Φ (empRisk r f S) rhoBar y,
            ∃ b ∈ proxSet Φ (popRisk P r f) rhoBar y,
              Real.sqrt (4 * (σ + s) ^ 2 / (α * (rhoBar - ρ) ^ 2 * m))
                + 2 * rhoBar * δ / (α * (rhoBar - ρ)) < ‖a - b‖}
        ≤ (T.card : ENNReal) *
            ENNReal.ofReal (Real.exp (-((m : ℝ) * (lam * (s / Real.sqrt m) - logMGFSym P L lam))))) ∧
    (0 < ρ → DifferentiableOn ℝ (fderiv ℝ Φ.val) (interior Φ.dom) →
      (∀ y ∈ C, HessInvertible Φ y) →
      (Measure.pi fun _ : Fin m => P)
          {S | ∃ y ∈ C, Real.sqrt (16 * (σ + s) ^ 2 / (α * m)) + 8 * ρ * δ / α <
            localDualNorm Φ y (fderiv ℝ (envelope Φ (empRisk r f S) (2 * ρ)) y
              - fderiv ℝ (envelope Φ (popRisk P r f) (2 * ρ)) y)}
        ≤ (T.card : ENNReal) *
            ENNReal.ofReal (Real.exp (-((m : ℝ) * (lam * (s / Real.sqrt m) - logMGFSym P L lam))))) := by
  exact ⟨GraphConvSubgrad.StatConc.Lib.part1 P Φ r f L ρ α σ hA C δ s hs m hm T hnet lam hlam,
    GraphConvSubgrad.StatConc.Lib.part2 P Φ r f L ρ α σ hA C hC δ s hs m hm T hnet lam hlam⟩
