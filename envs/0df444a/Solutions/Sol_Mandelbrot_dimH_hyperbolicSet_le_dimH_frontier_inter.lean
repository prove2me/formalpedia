-- Prove2me | solution 1 for Mandelbrot.dimH_hyperbolicSet_le_dimH_frontier_inter
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-26T13:28:54.426291+00:00
-- url     : https://prove2.me/submissions/3c01544f-ae0f-46bf-b076-01153ff3f3f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mandelbrot_hyperbolic_sets
import Theorems.Thm_Mandelbrot_hyperbolicSet_holomorphicMotion
import Theorems.Thm_HolomorphicMotion_holder_of_isCompact
import Theorems.Thm_HolomorphicMotion_iInf_dimH_inter_ball_le_dimH
import Theorems.Thm_Mandelbrot_exists_iterate_zero_eq_of_mem_frontier

open Topology Set Function Filter Bornology Metric MeasureTheory

namespace Mandelbrot

/-! ### Escape estimates for `z ↦ z ^ 2 + c` -/

lemma norm_iterate_ge_of_norm_gt (c w : ℂ) (hw : max 2 ‖c‖ < ‖w‖) (n : ℕ) :
    (‖w‖ - 1) ^ n * ‖w‖ ≤ ‖(fun z ↦ z ^ 2 + c)^[n] w‖ ∧ ‖w‖ ≤ ‖(fun z ↦ z ^ 2 + c)^[n] w‖ := by
  have h2 : 2 < ‖w‖ := (le_max_left _ _).trans_lt hw
  have hc : ‖c‖ < ‖w‖ := (le_max_right _ _).trans_lt hw
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [iterate_succ_apply']
    set y := (fun z ↦ z ^ 2 + c)^[n] w
    have hy : ‖y‖ ^ 2 - ‖c‖ ≤ ‖y ^ 2 + c‖ := by
      have := norm_add_le (y ^ 2 + c) (-c)
      simp only [add_neg_cancel_right, norm_pow, norm_neg] at this
      linarith
    have hq : 0 ≤ (‖w‖ - 1) ^ n * ‖w‖ :=
      mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)
    show _ ≤ ‖y ^ 2 + c‖ ∧ _ ≤ ‖y ^ 2 + c‖
    constructor
    · rw [pow_succ]
      nlinarith
    · nlinarith

lemma tendsto_iterate_of_norm_gt (c w : ℂ) (hw : max 2 ‖c‖ < ‖w‖) :
    Tendsto (fun n ↦ (fun z ↦ z ^ 2 + c)^[n] w) atTop (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h2 : 2 < ‖w‖ := (le_max_left _ _).trans_lt hw
  refine tendsto_atTop_mono (fun n => (norm_iterate_ge_of_norm_gt c w hw n).1) ?_
  exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).atTop_mul_const (by linarith)

lemma norm_le_of_bddAbove_orbit (c w : ℂ) (B : ℝ)
    (hB : ∀ n, ‖(fun z ↦ z ^ 2 + c)^[n] w‖ ≤ B) : ‖w‖ ≤ max 2 ‖c‖ := by
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := ((tendsto_norm_atTop_iff_cobounded.2
    (tendsto_iterate_of_norm_gt c w h)).eventually_gt_atTop B).exists
  linarith [hB n]

lemma norm_iterate_le_of_mem (c : ℂ) (hc : c ∈ mandelbrotSet) (n : ℕ) :
    ‖(fun z ↦ z ^ 2 + c)^[n] 0‖ ≤ max 2 ‖c‖ := by
  by_contra h
  push_neg at h
  apply hc
  have := tendsto_iterate_of_norm_gt c _ h
  rw [← tendsto_add_atTop_iff_nat n]
  simpa [← iterate_add_apply] using this

lemma mem_of_bddAbove_orbit (c : ℂ) (B : ℝ)
    (hB : ∀ n, ‖(fun z ↦ z ^ 2 + c)^[n] 0‖ ≤ B) : c ∈ mandelbrotSet := by
  intro h
  obtain ⟨n, hn⟩ := ((tendsto_norm_atTop_iff_cobounded.2 h).eventually_gt_atTop B).exists
  linarith [hB n]

/-- Points of a compact forward invariant set have norm at most `max 2 ‖c‖`. -/
lemma norm_le_of_mem_invariant (c : ℂ) (L : Set ℂ) (hL : IsCompact L)
    (hmaps : MapsTo (fun z ↦ z ^ 2 + c) L L) {w : ℂ} (hw : w ∈ L) : ‖w‖ ≤ max 2 ‖c‖ := by
  obtain ⟨B, hB⟩ := hL.isBounded.exists_norm_le
  exact norm_le_of_bddAbove_orbit c w B fun n => hB _ (hmaps.iterate n hw)

/-! ### Derivatives of iterates -/

lemma hasDerivAt_iterate_sq_add (c : ℂ) (n : ℕ) (y : ℂ) :
    HasDerivAt ((fun z ↦ z ^ 2 + c)^[n])
      (∏ j ∈ Finset.range n, 2 * (fun z ↦ z ^ 2 + c)^[j] y) y := by
  induction n with
  | zero => simpa using hasDerivAt_id y
  | succ n ih =>
    rw [iterate_succ', Finset.prod_range_succ, mul_comm]
    have h : HasDerivAt (fun z : ℂ ↦ z ^ 2 + c) (2 * (fun z ↦ z ^ 2 + c)^[n] y)
        ((fun z ↦ z ^ 2 + c)^[n] y) := by
      simpa using ((hasDerivAt_pow 2 ((fun z ↦ z ^ 2 + c)^[n] y)).add_const c)
    exact h.comp y ih

lemma differentiable_iterate_zero {n : ℕ} :
    Differentiable ℂ (fun c : ℂ ↦ (fun z ↦ z ^ 2 + c)^[n] 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iterate_succ_apply']
    exact (ih.pow 2).add differentiable_id

/-- Along an orbit in a hyperbolic set, the derivatives of the iterates are unbounded. -/
lemma unbounded_deriv_of_isHyperbolicSet (c : ℂ) (L : Set ℂ) (hL : IsHyperbolicSet c L)
    {w : ℂ} (hw : w ∈ L) (B : ℝ) :
    ∃ k, B < ‖∏ j ∈ Finset.range k, 2 * (fun z ↦ z ^ 2 + c)^[j] w‖ := by
  obtain ⟨hLc, hLm, n, -, hexp⟩ := hL
  set F : ℂ → ℝ := fun y ↦ ‖∏ j ∈ Finset.range n, 2 * (fun z ↦ z ^ 2 + c)^[j] y‖ with hF
  have hFd : ∀ y, F y = ‖deriv (fun z ↦ z ^ 2 + c)^[n] y‖ := fun y => by
    rw [(hasDerivAt_iterate_sq_add c n y).deriv]
  have hcont_it : ∀ j, Continuous ((fun z : ℂ ↦ z ^ 2 + c)^[j]) := fun j =>
    (by continuity : Continuous (fun z : ℂ ↦ z ^ 2 + c)).iterate j
  have hFc : Continuous F := by
    refine continuous_norm.comp ?_
    exact continuous_finset_prod _ fun j _ => continuous_const.mul (hcont_it j)
  obtain ⟨y₀, hy₀, hmin⟩ := hLc.exists_isMinOn ⟨w, hw⟩ hFc.continuousOn
  have hm : 1 < F y₀ := by rw [hFd]; exact hexp y₀ hy₀
  have hmL : ∀ y ∈ L, F y₀ ≤ F y := fun y hy => hmin hy
  have key : ∀ k, ∀ y ∈ L,
      F y₀ ^ k ≤ ‖∏ j ∈ Finset.range (n * k), 2 * (fun z ↦ z ^ 2 + c)^[j] y‖ := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      rw [mul_add, mul_one, Finset.prod_range_add, norm_mul, pow_succ]
      have h2 : ∏ i ∈ Finset.range n, 2 * (fun z ↦ z ^ 2 + c)^[n * k + i] y
          = ∏ i ∈ Finset.range n,
              2 * (fun z ↦ z ^ 2 + c)^[i] ((fun z ↦ z ^ 2 + c)^[n * k] y) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [add_comm, iterate_add_apply]
      rw [h2]
      have h3 := hmL _ (hLm.iterate (n * k) hy)
      exact mul_le_mul (ih y hy) h3 (by linarith) (norm_nonneg _)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hm
  exact ⟨n * k, hk.trans_le (key k w hw)⟩

/-! ### Complex analysis -/

/-- If `D` has a zero of finite order at `l` and `‖D * P k‖ ≤ B` on a disc for all `k`, then the
values `P k l` are bounded. -/
lemma bdd_of_mul_bdd (D : ℂ → ℂ) (l : ℂ) (hD : AnalyticAt ℂ D l)
    (hne : ¬ ∀ᶠ c in 𝓝 l, D c = 0) (s : ℝ) (hs : 0 < s) (P : ℕ → ℂ → ℂ)
    (hP : ∀ k, DifferentiableOn ℂ (P k) (ball l s)) (B : ℝ)
    (hB : ∀ k, ∀ c ∈ ball l s, ‖D c * P k c‖ ≤ B) : ∃ M, ∀ k, ‖P k l‖ ≤ M := by
  obtain ⟨m, E, hE, hEl, hfac⟩ := hD.exists_eventuallyEq_pow_smul_nonzero_iff.2 hne
  have hev : ∀ᶠ z in 𝓝 l, D z = (z - l) ^ m • E z ∧ DifferentiableAt ℂ E z :=
    hfac.and (hE.eventually_analyticAt.mono fun z hz => hz.differentiableAt)
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.1 hev
  set r := min (ε / 2) (s / 2) with hr_def
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
  have hrs : r < s := (min_le_right _ _).trans_lt (by linarith)
  have hmem : ∀ z ∈ closedBall l r, dist z l < ε ∧ z ∈ ball l s := fun z hz =>
    ⟨(mem_closedBall.1 hz).trans_lt hrε, mem_ball.2 ((mem_closedBall.1 hz).trans_lt hrs)⟩
  have hrm : 0 < r ^ m := pow_pos hr m
  refine ⟨B / r ^ m / ‖E l‖, fun k => ?_⟩
  have hdiff : DifferentiableOn ℂ (fun z ↦ E z * P k z) (closedBall l r) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hmem z hz
    exact ((hεp h1).2.differentiableWithinAt).mul
      ((hP k).mono (closedBall_subset_ball hrs) z hz)
  have hmax : ‖(fun z ↦ E z * P k z) l‖ ≤ B / r ^ m := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun z ↦ E z * P k z)
      (U := ball l r) isBounded_ball
      (by rw [← closure_ball l hr.ne'] at hdiff; exact hdiff.diffContOnCl) ?_
      (subset_closure (mem_ball_self hr))
    intro z hz
    rw [frontier_ball l hr.ne'] at hz
    have hzc : z ∈ closedBall l r := sphere_subset_closedBall hz
    obtain ⟨h1, h2⟩ := hmem z hzc
    have hD' := (hεp h1).1
    have hBz := hB k z h2
    rw [hD', smul_eq_mul, mul_assoc, norm_mul, norm_pow, ← dist_eq_norm,
      mem_sphere.1 hz] at hBz
    rw [le_div_iff₀ hrm, mul_comm]
    exact hBz
  simp only [norm_mul] at hmax
  have hEl' : 0 < ‖E l‖ := norm_pos_iff.2 hEl
  rw [le_div_iff₀ hEl', mul_comm]
  exact hmax

/-! ### Dimension theory -/

lemma ofReal_mul_dimH_le_dimH_image (g : ℂ → ℂ) (Y : Set ℂ) (C α : ℝ) (hα : 0 < α)
    (h : ∀ z ∈ Y, ∀ w ∈ Y, dist z w ≤ C * dist (g z) (g w) ^ α) :
    ENNReal.ofReal α * dimH Y ≤ dimH (g '' Y) := by
  set C' := max C 0
  have h' : ∀ z ∈ Y, ∀ w ∈ Y, dist z w ≤ C' * dist (g z) (g w) ^ α := fun z hz w hw =>
    (h z hz w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg dist_nonneg _))
  have hinj : InjOn g Y := by
    intro z hz w hw hzw
    have := h' z hz w hw
    rw [hzw, dist_self, Real.zero_rpow hα.ne', mul_zero] at this
    exact dist_le_zero.1 this
  have hleft := hinj.leftInvOn_invFunOn
  have hhold : HolderOnWith (Real.toNNReal C') (Real.toNNReal α) (invFunOn g Y) (g '' Y) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hleft hz, hleft hw, edist_dist, edist_dist, Real.coe_toNNReal _ hα.le,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal C' * _
    rw [← ENNReal.ofReal_mul (le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal (h' z hz w hw)
  have := hhold.dimH_image_le (Real.toNNReal_pos.2 hα)
  rw [hleft.image_image] at this
  have hne0 : ((Real.toNNReal α : NNReal) : ENNReal) ≠ 0 := by simpa using hα
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl ENNReal.coe_ne_top), mul_comm] at this
  exact this

/-! ### The holomorphic motion of a hyperbolic set -/

section Motion

variable {c₀ : ℂ} {K : Set ℂ} {ρ : ℝ} {ι : ℂ → ℂ → ℂ}

lemma iterate_motion (hKm : MapsTo (fun z ↦ z ^ 2 + c₀) K K)
    (hconj : ∀ c ∈ ball c₀ ρ, ∀ z ∈ K, ι c (z ^ 2 + c₀) = ι c z ^ 2 + c)
    {c : ℂ} (hc : c ∈ ball c₀ ρ) {z : ℂ} (hz : z ∈ K) (k : ℕ) :
    (fun w ↦ w ^ 2 + c)^[k] (ι c z) = ι c ((fun w ↦ w ^ 2 + c₀)^[k] z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, iterate_succ_apply',
      hconj c hc _ (hKm.iterate k hz)]

lemma norm_motion_le (hK : IsCompact K) (hKm : MapsTo (fun z ↦ z ^ 2 + c₀) K K)
    (hcont : ∀ c ∈ ball c₀ ρ, ContinuousOn (ι c) K)
    (hconj : ∀ c ∈ ball c₀ ρ, ∀ z ∈ K, ι c (z ^ 2 + c₀) = ι c z ^ 2 + c)
    {c : ℂ} (hc : c ∈ ball c₀ ρ) {z : ℂ} (hz : z ∈ K) : ‖ι c z‖ ≤ max 2 ‖c‖ := by
  refine norm_le_of_mem_invariant c (ι c '' K) (hK.image_of_continuousOn (hcont c hc)) ?_
    (mem_image_of_mem _ hz)
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y ^ 2 + c₀, hKm hy, hconj c hc y hy⟩

lemma mem_of_iterate_eq_motion (hK : IsCompact K) (hKm : MapsTo (fun z ↦ z ^ 2 + c₀) K K)
    (hcont : ∀ c ∈ ball c₀ ρ, ContinuousOn (ι c) K)
    (hconj : ∀ c ∈ ball c₀ ρ, ∀ z ∈ K, ι c (z ^ 2 + c₀) = ι c z ^ 2 + c)
    {c : ℂ} (hc : c ∈ ball c₀ ρ) {z : ℂ} (hz : z ∈ K) {N : ℕ}
    (hN : (fun w ↦ w ^ 2 + c)^[N] 0 = ι c z) : c ∈ mandelbrotSet := by
  refine mem_of_bddAbove_orbit c
    (∑ n ∈ Finset.range N, ‖(fun w ↦ w ^ 2 + c)^[n] 0‖ + max 2 ‖c‖) fun n => ?_
  rcases lt_or_ge n N with hn | hn
  · have := Finset.single_le_sum (f := fun n ↦ ‖(fun w ↦ w ^ 2 + c)^[n] 0‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 hn)
    have h2 : (0 : ℝ) ≤ max 2 ‖c‖ := le_max_of_le_left zero_le_two
    exact le_add_of_le_of_nonneg this h2
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm, iterate_add_apply, hN, iterate_motion hKm hconj hc hz]
    have h1 := norm_motion_le hK hKm hcont hconj hc (hKm.iterate k hz)
    have h2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, ‖(fun w ↦ w ^ 2 + c)^[n] 0‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith

/-- The critical orbit cannot follow a point of the moving set identically on the whole disc. -/
lemma not_forall_iterate_eq_motion (hc₀ : c₀ ∈ frontier mandelbrotSet) (hρ : 0 < ρ)
    (hK : IsCompact K) (hKm : MapsTo (fun z ↦ z ^ 2 + c₀) K K)
    (hcont : ∀ c ∈ ball c₀ ρ, ContinuousOn (ι c) K)
    (hconj : ∀ c ∈ ball c₀ ρ, ∀ z ∈ K, ι c (z ^ 2 + c₀) = ι c z ^ 2 + c)
    {z : ℂ} (hz : z ∈ K) (N : ℕ) :
    ¬ ∀ c ∈ ball c₀ ρ, (fun w ↦ w ^ 2 + c)^[N] 0 = ι c z := by
  intro h
  have hsub : ball c₀ ρ ⊆ mandelbrotSet := fun c hc =>
    mem_of_iterate_eq_motion hK hKm hcont hconj hc hz (h c hc)
  exact hc₀.2 (mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (ball_mem_nhds c₀ hρ) hsub))

/-- Identity theorem version: the critical orbit cannot follow a point of the moving set on any
neighbourhood of a parameter of the disc. -/
lemma not_eventually_iterate_eq_motion (hc₀ : c₀ ∈ frontier mandelbrotSet) (hρ : 0 < ρ)
    (hK : IsCompact K) (hKm : MapsTo (fun z ↦ z ^ 2 + c₀) K K)
    (hhol : ∀ z ∈ K, DifferentiableOn ℂ (fun c ↦ ι c z) (ball c₀ ρ))
    (hcont : ∀ c ∈ ball c₀ ρ, ContinuousOn (ι c) K)
    (hconj : ∀ c ∈ ball c₀ ρ, ∀ z ∈ K, ι c (z ^ 2 + c₀) = ι c z ^ 2 + c)
    {z : ℂ} (hz : z ∈ K) (N : ℕ) {l : ℂ} (hl : l ∈ ball c₀ ρ) :
    ¬ ∀ᶠ c in 𝓝 l, (fun w ↦ w ^ 2 + c)^[N] 0 - ι c z = 0 := by
  intro hev
  have hF : AnalyticOnNhd ℂ (fun c ↦ (fun w ↦ w ^ 2 + c)^[N] 0 - ι c z) (ball c₀ ρ) :=
    (differentiable_iterate_zero.differentiableOn.sub (hhol z hz)).analyticOnNhd isOpen_ball
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball c₀ ρ).isPreconnected hl hev
  exact not_forall_iterate_eq_motion hc₀ hρ hK hKm hcont hconj hz N fun c hc =>
    sub_eq_zero.1 (heq hc)

/-- If the critical orbit lands in the moving hyperbolic set, the parameter is in `∂M`. -/
lemma mem_frontier_of_iterate_eq_motion (hc₀ : c₀ ∈ frontier mandelbrotSet) (hρ : 0 < ρ)
    (hK : IsCompact K) (hKm : MapsTo (fun z ↦ z ^ 2 + c₀) K K)
    (hhol : ∀ z ∈ K, DifferentiableOn ℂ (fun c ↦ ι c z) (ball c₀ ρ))
    (hcont : ∀ c ∈ ball c₀ ρ, ContinuousOn (ι c) K)
    (hconj : ∀ c ∈ ball c₀ ρ, ∀ z ∈ K, ι c (z ^ 2 + c₀) = ι c z ^ 2 + c)
    (hhyp : ∀ c ∈ ball c₀ ρ, IsHyperbolicSet c (ι c '' K))
    {l : ℂ} (hl : l ∈ ball c₀ ρ) {z : ℂ} (hz : z ∈ K) {N : ℕ}
    (hN : (fun w ↦ w ^ 2 + l)^[N] 0 = ι l z) : l ∈ frontier mandelbrotSet := by
  refine ⟨subset_closure (mem_of_iterate_eq_motion hK hKm hcont hconj hl hz hN), fun hint => ?_⟩
  obtain ⟨s₀, hs₀, hs₀M⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  set s₁ := ρ - dist l c₀ with hs₁
  have hs₁pos : 0 < s₁ := by rw [mem_ball] at hl; linarith
  set s := min s₀ s₁ with hs_def
  have hs : 0 < s := lt_min hs₀ hs₁pos
  have hsM : ball l s ⊆ mandelbrotSet := (ball_subset_ball (min_le_left _ _)).trans hs₀M
  have hsρ : ball l s ⊆ ball c₀ ρ :=
    (ball_subset_ball (min_le_right _ _)).trans (ball_subset_ball' (by rw [hs₁]; linarith))
  set D : ℂ → ℂ := fun c ↦ (fun w ↦ w ^ 2 + c)^[N] 0 - ι c z with hD_def
  have hD : AnalyticAt ℂ D l :=
    (differentiable_iterate_zero.differentiableOn.sub (hhol z hz)).analyticAt
      (isOpen_ball.mem_nhds hl)
  have hne := not_eventually_iterate_eq_motion hc₀ hρ hK hKm hhol hcont hconj hz N hl
  set P : ℕ → ℂ → ℂ := fun k c ↦ ∏ j ∈ Finset.range k,
    ((fun w ↦ w ^ 2 + c)^[N + j] 0 + ι c ((fun w ↦ w ^ 2 + c₀)^[j] z)) with hP_def
  have hP : ∀ k, DifferentiableOn ℂ (P k) (ball l s) := fun k =>
    DifferentiableOn.fun_finset_prod fun j _ =>
      differentiable_iterate_zero.differentiableOn.add
        ((hhol _ (hKm.iterate j hz)).mono hsρ)
  have hid : ∀ c ∈ ball c₀ ρ, ∀ k, (fun w ↦ w ^ 2 + c)^[N + k] 0 -
      ι c ((fun w ↦ w ^ 2 + c₀)^[k] z) = D c * P k c := by
    intro c hc k
    induction k with
    | zero => simp [hD_def, hP_def]
    | succ k ih =>
      simp only [hP_def, Finset.prod_range_succ] at ih ⊢
      rw [← add_assoc, iterate_succ_apply', iterate_succ_apply',
        hconj c hc _ (hKm.iterate k hz), ← mul_assoc, ← ih]
      ring
  set B := 2 * max 2 (‖l‖ + s) with hB_def
  have hB : ∀ k, ∀ c ∈ ball l s, ‖D c * P k c‖ ≤ B := by
    intro k c hc
    rw [← hid c (hsρ hc) k]
    have hcn : ‖c‖ ≤ ‖l‖ + s := by
      have := norm_le_norm_add_norm_sub' c l
      rw [← dist_eq_norm] at this
      linarith [mem_ball.1 hc]
    have hmax : max 2 ‖c‖ ≤ max 2 (‖l‖ + s) := max_le_max le_rfl hcn
    have h1 := norm_iterate_le_of_mem c (hsM hc) (N + k)
    have h2 := norm_motion_le hK hKm hcont hconj (hsρ hc) (hKm.iterate k hz)
    have h3 := norm_sub_le ((fun w ↦ w ^ 2 + c)^[N + k] 0) (ι c ((fun w ↦ w ^ 2 + c₀)^[k] z))
    linarith
  obtain ⟨M, hM⟩ := bdd_of_mul_bdd D l hD hne s hs P hP B hB
  have hPl : ∀ k, P k l = ∏ j ∈ Finset.range k, 2 * (fun w ↦ w ^ 2 + l)^[j] (ι l z) := by
    intro k
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [add_comm N j, iterate_add_apply, hN, ← iterate_motion hKm hconj hl hz, two_mul]
  obtain ⟨k, hk⟩ := unbounded_deriv_of_isHyperbolicSet l _ (hhyp l hl) (mem_image_of_mem _ hz) M
  have := hM k
  rw [hPl] at this
  linarith

end Motion

/-! ### The main theorem -/

lemma ofReal_mul_le_dimH (c : ℂ) (hc : c ∈ frontier mandelbrotSet)
    (K : Set ℂ) (hK : IsHyperbolicSet c K) (U : Set ℂ) (hU : U ∈ 𝓝 c)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (r : ENNReal) (hr : r < dimH K) :
    ENNReal.ofReal α * r ≤ dimH (frontier mandelbrotSet ∩ U) := by
  obtain ⟨ρ, hρ, ι, h0, hinj, hhol, hcont, hconj, hhyp⟩ := hyperbolicSet_holomorphicMotion c K hK
  obtain ⟨hKc, hKm, -⟩ := hK
  obtain ⟨z₀, hz₀K, hz₀⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hr
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨δ, hδ, hhold⟩ := HolomorphicMotion.holder_of_isCompact K hKc c ρ hρ ι h0 hinj hhol α hα0 hα1
  set ρ₁ := min ρ (min ε δ) with hρ₁_def
  have hρ₁ : 0 < ρ₁ := lt_min hρ (lt_min hε hδ)
  have hρ₁ρ : ball c ρ₁ ⊆ ball c ρ := ball_subset_ball (min_le_left _ _)
  have hρ₁ε : ball c ρ₁ ⊆ U :=
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))).trans hεU
  have hρ₁δ : ball c ρ₁ ⊆ ball c δ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have ha : AnalyticAt ℂ (fun l ↦ ι l z₀) c := (hhol z₀ hz₀K).analyticAt (ball_mem_nhds c hρ)
  obtain ⟨c₁, hc₁, N, hN⟩ :=
    exists_iterate_zero_eq_of_mem_frontier c hc _ ha (ball c ρ₁) (ball_mem_nhds c hρ₁)
  set R₁ := ρ₁ - dist c₁ c with hR₁_def
  have hR₁ : 0 < R₁ := by rw [mem_ball] at hc₁; linarith
  have hsub : ball c₁ R₁ ⊆ ball c ρ₁ := ball_subset_ball' (by rw [hR₁_def]; linarith)
  have hc₁ρ : c₁ ∈ ball c ρ := hρ₁ρ hc₁
  -- the motion rebased at `c₁`
  set X₁ := ι c₁ '' K with hX₁
  set g := invFunOn (ι c₁) K with hg
  set ι' : ℂ → ℂ → ℂ := fun l w ↦ ι l (g w) with hι'
  have hgX : ∀ w ∈ X₁, g w ∈ K ∧ ι c₁ (g w) = w := fun w hw =>
    ⟨invFunOn_mem hw, invFunOn_eq hw⟩
  have hgz : g (ι c₁ z₀) = z₀ :=
    (hinj c₁ hc₁ρ).leftInvOn_invFunOn hz₀K
  set v : ℂ → ℂ := fun l ↦ (fun w ↦ w ^ 2 + l)^[N] 0 with hv_def
  have h0' : ∀ w ∈ X₁, ι' c₁ w = w := fun w hw => (hgX w hw).2
  have hinj' : ∀ l ∈ ball c₁ R₁, InjOn (ι' l) X₁ := by
    intro l hl w₁ hw₁ w₂ hw₂ h
    have h' : g w₁ = g w₂ := hinj l (hρ₁ρ (hsub hl)) (hgX w₁ hw₁).1 (hgX w₂ hw₂).1 h
    rw [← (hgX w₁ hw₁).2, ← (hgX w₂ hw₂).2, h']
  have hhol' : ∀ w ∈ X₁, DifferentiableOn ℂ (fun l ↦ ι' l w) (ball c₁ R₁) := fun w hw =>
    (hhol (g w) (hgX w hw).1).mono (hsub.trans hρ₁ρ)
  have hv : DifferentiableOn ℂ v (ball c₁ R₁) := differentiable_iterate_zero.differentiableOn
  have hne : ∃ l ∈ ball c₁ R₁, v l ≠ ι' l (ι c₁ z₀) := by
    by_contra hcon
    push_neg at hcon
    apply not_eventually_iterate_eq_motion hc hρ hKc hKm hhol hcont hconj hz₀K N hc₁ρ
    filter_upwards [ball_mem_nhds c₁ hR₁] with l hl
    have := hcon l hl
    simp only [hι', hgz] at this
    simp only [hv_def] at this
    rw [this, sub_self]
  have key := HolomorphicMotion.iInf_dimH_inter_ball_le_dimH X₁ c₁ R₁ ι' h0' hinj' hhol' v hv (ι c₁ z₀)
    ⟨z₀, hz₀K, rfl⟩ hN hne
  -- the parameter set lies in `∂M ∩ U`
  have hS : {l ∈ ball c₁ R₁ | v l ∈ ι' l '' X₁} ⊆ frontier mandelbrotSet ∩ U := by
    rintro l ⟨hl, w, hw, hvw⟩
    refine ⟨?_, hρ₁ε (hsub hl)⟩
    exact mem_frontier_of_iterate_eq_motion hc hρ hKc hKm hhol hcont hconj hhyp
      (hρ₁ρ (hsub hl)) (hgX w hw).1 hvw.symm
  -- lower bound on the local dimension of the rebased set
  obtain ⟨C, hC⟩ := hhold c₁ (hρ₁δ hc₁)
  have hlow : ENNReal.ofReal α * r ≤ ⨅ r' > (0 : ℝ), dimH (X₁ ∩ ball (ι c₁ z₀) r') := by
    refine le_iInf₂ fun r' hr' => ?_
    obtain ⟨η, hη, hηr⟩ := Metric.continuousWithinAt_iff.1
      ((hcont c₁ hc₁ρ) z₀ hz₀K) r' hr'
    have h1 : r < dimH (K ∩ ball z₀ η) :=
      hz₀ _ (inter_mem_nhdsWithin K (ball_mem_nhds z₀ hη))
    have h2 := ofReal_mul_dimH_le_dimH_image (ι c₁) (K ∩ ball z₀ η) C α hα0
      (fun z hz w hw => (hC z hz.1 w hw.1).2)
    have h3 : ι c₁ '' (K ∩ ball z₀ η) ⊆ X₁ ∩ ball (ι c₁ z₀) r' := by
      rintro _ ⟨z, ⟨hzK, hzη⟩, rfl⟩
      exact ⟨mem_image_of_mem _ hzK, hηr hzK hzη⟩
    calc ENNReal.ofReal α * r ≤ ENNReal.ofReal α * dimH (K ∩ ball z₀ η) := by gcongr
      _ ≤ dimH (ι c₁ '' (K ∩ ball z₀ η)) := h2
      _ ≤ _ := dimH_mono h3
  exact hlow.trans (key.trans (dimH_mono hS))

theorem dimH_hyperbolicSet_le_dimH_frontier_inter_aux (c : ℂ) (hc : c ∈ frontier mandelbrotSet)
    (K : Set ℂ) (hK : IsHyperbolicSet c K) (U : Set ℂ) (hU : U ∈ 𝓝 c) :
    dimH K ≤ dimH (frontier mandelbrotSet ∩ U) := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  have hat : a ≠ ⊤ := ha.trans ENNReal.one_lt_top |>.ne
  have h := ofReal_mul_le_dimH c hc K hK U hU a.toReal
    (ENNReal.toReal_pos ha0 hat) ((ENNReal.toReal_lt_toReal hat ENNReal.one_ne_top).2 ha |>.trans_eq
      ENNReal.toReal_one) r hr
  rwa [ENNReal.ofReal_toReal hat] at h

end Mandelbrot

open Mandelbrot

theorem solution (c : ℂ) (hc : c ∈ frontier mandelbrotSet)
    (K : Set ℂ) (hK : IsHyperbolicSet c K) (U : Set ℂ) (hU : U ∈ 𝓝 c) :
    dimH K ≤ dimH (frontier mandelbrotSet ∩ U) :=
  Mandelbrot.dimH_hyperbolicSet_le_dimH_frontier_inter_aux c hc K hK U hU
