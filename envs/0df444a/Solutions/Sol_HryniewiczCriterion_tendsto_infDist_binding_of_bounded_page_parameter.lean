-- Prove2me | solution 1 for HryniewiczCriterion.tendsto_infDist_binding_of_bounded_page_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T16:18:08.765204+00:00
-- url     : https://prove2.me/submissions/ba0e4e54-d5f9-4dda-8414-453d0759c554

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Theorems.Thm_exists_contDiffAt_leftInverse_of_injective_fderiv
import Theorems.Thm_HryniewiczCriterion_exists_forall_mem_of_injOn_closedUnitDisk
import Theorems.Thm_HryniewiczCriterion_exists_fderiv_page_eq_hamiltonianVectorField
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open HryniewiczCriterion
open scoped ContDiff
open scoped ContDiff Topology
open Filter

namespace HryniewiczCriterion

lemma rb1_isClosed_closedUnitDisk : IsClosed closedUnitDisk :=
  isClosed_le (by fun_prop) continuous_const

lemma rb1_isOpen_openUnitDisk : IsOpen openUnitDisk :=
  isOpen_lt (by fun_prop) continuous_const

lemma rb1_isCompact_closedUnitDisk : IsCompact closedUnitDisk := by
  refine Metric.isCompact_of_isClosed_isBounded rb1_isClosed_closedUnitDisk ?_
  refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 1)).subset ?_
  intro u hu
  have hu' : u 0 ^ 2 + u 1 ^ 2 ≤ 1 := hu
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  fin_cases i <;> simp <;> constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

lemma rb1_openUnitDisk_subset : openUnitDisk ⊆ closedUnitDisk := fun u hu =>
  le_of_lt (show u 0 ^ 2 + u 1 ^ 2 < 1 from hu)

/-- Every unit vector is `(cos 2πt, sin 2πt)`. -/
lemma rb1_cos_sin (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ t : ℝ, Real.cos (2 * Real.pi * t) = a ∧ Real.sin (2 * Real.pi * t) = b := by
  set z : ℂ := ⟨a, b⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [z, ← sq, h]
  have hz : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  refine ⟨Complex.arg z / (2 * Real.pi), ?_, ?_⟩
  · rw [mul_div_cancel₀ _ (by positivity), Complex.cos_arg hz, hn, div_one]
  · rw [mul_div_cancel₀ _ (by positivity), Complex.sin_arg, hn, div_one]

/-- A point of the closed disk off the open disk is a circle point. -/
lemma rb1_exists_circlePoint {v : Plane} (hv : v ∈ closedUnitDisk) (hv' : v ∉ openUnitDisk) :
    ∃ t, v = circlePoint t := by
  have h1 : v 0 ^ 2 + v 1 ^ 2 ≤ 1 := hv
  have h2 : ¬ v 0 ^ 2 + v 1 ^ 2 < 1 := hv'
  obtain ⟨t, ht1, ht2⟩ := rb1_cos_sin (v 0) (v 1) (by linarith [not_lt.1 h2])
  refine ⟨t, ?_⟩
  ext j; fin_cases j
  · simp [circlePoint, ht1]
  · simp [circlePoint, ht2]

/-- `dH(x)(X_H(x)) = 0`. -/
lemma rb1_dH_hvf (H : R4 → ℝ) (x : R4) :
    fderiv ℝ H x (hamiltonianVectorField H x) = 0 := by
  set X := hamiltonianVectorField H x
  have hX : X = ∑ i : Fin 4, X i • (Pi.single i (1 : ℝ) : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  rw [hX, map_sum]
  simp only [map_smul, smul_eq_mul, Fin.sum_univ_four]
  simp [X, hamiltonianVectorField, partialDeriv]
  ring

lemma rb1_continuous_hvf {H : R4 → ℝ} (hH : ContDiff ℝ ∞ H) :
    Continuous (hamiltonianVectorField H) := by
  have hc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have hp : ∀ i, Continuous fun x => partialDeriv H x i := fun i =>
    hc.clm_apply continuous_const
  refine continuous_pi fun j => ?_
  fin_cases j
  · exact (hp 1).neg
  · exact hp 0
  · exact (hp 3).neg
  · exact hp 2

end HryniewiczCriterion

namespace HryniewiczCriterion

/-- Near an open-disk page point `page θ₀ v₀`, a trajectory written on pages as
`y t = page (Θ t) (u t)` moves its page parameter by a definite amount over a fixed time,
as long as the parameter stays close to `θ₀`. -/
lemma rb1_core (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hinj : ∀ θ, Set.InjOn (page θ) closedUnitDisk)
    (hpS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    (y : ℝ → R4) (hy : IsTrajectory H y) (Θ : ℝ → ℝ) (u : ℝ → Plane)
    (hyu : ∀ t, u t ∈ closedUnitDisk ∧ page (Θ t) (u t) = y t)
    {θ₀ : ℝ} {v₀ : Plane} (hv₀ : v₀ ∈ openUnitDisk) :
    ∃ ρ > 0, ∃ η > 0, ∃ h > 0, ∃ c > 0, ∀ t, ‖y t - page θ₀ v₀‖ < ρ →
      (∀ s ∈ Set.Icc t (t + h), |Θ s - θ₀| < η) → c ≤ |Θ (t + h) - Θ t| := by
  set e : ℝ × Plane → R4 := fun z => page z.1 z.2 with he_def
  set p : ℝ × Plane := (θ₀, v₀)
  set z : R4 := page θ₀ v₀
  have hez : e p = z := rfl
  set X := hamiltonianVectorField H
  have hXc : Continuous X := rb1_continuous_hvf hS.1
  -- local left inverse
  obtain ⟨g, hg, hgl⟩ := exists_contDiffAt_leftInverse_of_injective_fderiv
    (hsm.contDiffAt (x := p)) (hreg θ₀ v₀ hv₀)
  rw [hez] at hg
  obtain ⟨η₀, hη₀, hrec⟩ := exists_forall_mem_of_injOn_closedUnitDisk (f := page) hsm.continuous (hinj θ₀)
    (rb1_openUnitDisk_subset hv₀) hgl
  -- the parameter component of `Dg(z) X(z)` is nonzero
  obtain ⟨w, hw, hw1⟩ := exists_fderiv_page_eq_hamiltonianVectorField H hS page hsm hpS htr hreg hv₀
  have hed : DifferentiableAt ℝ e p := (hsm.differentiable (by simp)) p
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by simp)
  have hid : (fderiv ℝ g z).comp (fderiv ℝ e p) = ContinuousLinearMap.id ℝ (ℝ × Plane) := by
    have h1 : HasFDerivAt (g ∘ e) ((fderiv ℝ g z).comp (fderiv ℝ e p)) p :=
      hgd.hasFDerivAt.comp p hed.hasFDerivAt
    have h2 : HasFDerivAt (g ∘ e) (ContinuousLinearMap.id ℝ (ℝ × Plane)) p :=
      (hasFDerivAt_id p).congr_of_eventuallyEq (by filter_upwards [hgl] with q hq; exact hq)
    exact h1.unique h2
  set φ : R4 → ℝ := fun x => (fderiv ℝ g x (X x)).1
  have hφz : φ z = w.1 := by
    simp only [φ]
    rw [show X z = fderiv ℝ e p w from hw.symm]
    have := congrArg (fun L : ℝ × Plane →L[ℝ] ℝ × Plane => (L w).1) hid
    simpa using this
  set a := w.1
  have ha : 0 < |a| := abs_pos.2 hw1
  have hφc : ContinuousAt φ z :=
    continuous_fst.continuousAt.comp ((hg.continuousAt_fderiv (by simp)).clm_apply hXc.continuousAt)
  have hev1 : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 1 g x := (hg.of_le (by simp)).eventually (by simp)
  have hev2 : ∀ᶠ x in 𝓝 z, |φ x - a| < |a| / 2 := by
    have := hφc.eventually (Metric.ball_mem_nhds (φ z) (half_pos ha))
    filter_upwards [this] with x hx
    simpa [Real.dist_eq, hφz] using hx
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
  set r := min ρ₁ η₀
  have hr : 0 < r := lt_min hρ₁ hη₀
  -- speed bound on the compact set of nearby pages
  set K : Set R4 := e '' (Set.Icc (θ₀ - η₀) (θ₀ + η₀) ×ˢ closedUnitDisk)
  have hK : IsCompact K :=
    (isCompact_Icc.prod rb1_isCompact_closedUnitDisk).image hsm.continuous
  have hzK : z ∈ K := ⟨p, ⟨⟨by linarith, by linarith⟩, rb1_openUnitDisk_subset hv₀⟩, rfl⟩
  obtain ⟨xm, -, hxm⟩ := hK.exists_isMaxOn ⟨z, hzK⟩ (continuous_norm.comp hXc).continuousOn
  set M := max ‖X xm‖ 1
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set h := r / (2 * M)
  have hh : 0 < h := div_pos hr (by positivity)
  refine ⟨r / 2, half_pos hr, η₀, hη₀, h, hh, |a| / 2 * h, by positivity, ?_⟩
  intro t ht hΘ
  -- the window stays in the ball
  have hspeed : ∀ s ∈ Set.Icc t (t + h), ‖X (y s)‖ ≤ M := by
    intro s hs
    have hyK : y s ∈ K := ⟨(Θ s, u s), ⟨⟨by linarith [(abs_lt.1 (hΘ s hs)).1],
      by linarith [(abs_lt.1 (hΘ s hs)).2]⟩, (hyu s).1⟩, (hyu s).2⟩
    exact le_trans (hxm hyK) (le_max_left _ _)
  have hin : ∀ s ∈ Set.Icc t (t + h), ‖y s - z‖ < r := by
    intro s hs
    have h1 : ‖y s - y t‖ ≤ M * ‖s - t‖ :=
      (convex_Icc t (t + h)).norm_image_sub_le_of_norm_hasDerivWithin_le (f := y)
        (fun x _ => (hy.1 x).hasDerivWithinAt) hspeed ⟨le_rfl, by linarith⟩ hs
    have h2 : ‖s - t‖ ≤ h := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have h3 : M * h = r / 2 := by simp only [h]; field_simp
    calc ‖y s - z‖ ≤ ‖y s - y t‖ + ‖y t - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < M * h + r / 2 := by nlinarith
      _ = r := by rw [h3]; ring
  have hfix : ∀ s ∈ Set.Icc t (t + h), (g (y s)).1 = Θ s := by
    intro s hs
    have hmem := hrec (Θ s) (u s) (hΘ s hs) (hyu s).1
      (by rw [(hyu s).2]; exact lt_of_lt_of_le (hin s hs) (min_le_right _ _))
    have : g (e (Θ s, u s)) = (Θ s, u s) := hmem
    simp only [e, (hyu s).2] at this
    rw [this]
  have hloc : ∀ s ∈ Set.Icc t (t + h), y s ∈ Metric.ball z ρ₁ := fun s hs => by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le (hin s hs) (min_le_left _ _)
  have hder : ∀ s ∈ Set.Icc t (t + h),
      HasDerivAt (fun s => (g (y s)).1) (φ (y s)) s := by
    intro s hs
    have hgs : DifferentiableAt ℝ g (y s) := ((hball (hloc s hs)).1).differentiableAt (by simp)
    have := (hasFDerivAt_fst.comp (y s) hgs.hasFDerivAt).comp_hasDerivAt s (hy.1 s)
    exact this
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun s => (g (y s)).1) (fun s => φ (y s))
    (by linarith : t < t + h)
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => hder s (Set.Ioo_subset_Icc_self hs))
  have hcI : c ∈ Set.Icc t (t + h) := Set.Ioo_subset_Icc_self hc
  rw [hfix t ⟨le_rfl, by linarith⟩, hfix (t + h) ⟨by linarith, le_rfl⟩, add_sub_cancel_left]
    at hcd
  have hφy : |a| / 2 ≤ |φ (y c)| := by
    have := (hball (hloc c hcI)).2
    have := abs_sub_abs_le_abs_sub a (φ (y c))
    rw [abs_sub_comm] at this
    linarith
  have hdiff : Θ (t + h) - Θ t = φ (y c) * h := by
    rw [hcd]; field_simp
  rw [hdiff, abs_mul, abs_of_pos hh]
  exact mul_le_mul_of_nonneg_right hφy hh.le

end HryniewiczCriterion

namespace HryniewiczCriterion

/-- One end of the trajectory: if the page parameter converges along the end `l`, the
trajectory accumulates on the binding along `l`. -/
lemma rb1_end (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hinj : ∀ θ, Set.InjOn (page θ) closedUnitDisk)
    (hpS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (hbind : ∀ θ t, page θ (circlePoint t) = P.x (P.T * t))
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    (y : ℝ → R4) (hy : IsTrajectory H y) (Θ : ℝ → ℝ) (u : ℝ → Plane)
    (hyu : ∀ t, u t ∈ closedUnitDisk ∧ page (Θ t) (u t) = y t)
    (l : Filter ℝ) [l.IsCountablyGenerated]
    (hl : ∀ h : ℝ, Tendsto (fun t => t + h) l l)
    (hwin : ∀ (Q : ℝ → Prop) (h : ℝ), 0 < h → (∀ᶠ s in l, Q s) →
      ∀ᶠ t in l, ∀ s ∈ Set.Icc t (t + h), Q s)
    {θs : ℝ} (hΘ : Tendsto Θ l (𝓝 θs)) :
    Tendsto (fun t => Metric.infDist (y t) P.image) l (𝓝 0) := by
  by_contra hnt
  have hfreq : ∃ ε > 0, ∃ᶠ t in l, ε ≤ Metric.infDist (y t) P.image := by
    by_contra hno
    push_neg at hno
    apply hnt
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hno ε hε] with t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    exact ht
  obtain ⟨ε, hε, hfr⟩ := hfreq
  obtain ⟨ts, hts, htsε⟩ := exists_seq_forall_of_frequently hfr
  obtain ⟨v, hv, φ, hφ, hφv⟩ := rb1_isCompact_closedUnitDisk.tendsto_subseq
    (x := fun n => u (ts n)) (fun n => (hyu (ts n)).1)
  have htsφ : Tendsto (ts ∘ φ) atTop l := hts.comp hφ.tendsto_atTop
  set z := page θs v
  have hyz : Tendsto (fun k => y (ts (φ k))) atTop (𝓝 z) := by
    have h1 : Tendsto (fun k => (Θ (ts (φ k)), u (ts (φ k)))) atTop (𝓝 (θs, v)) :=
      (hΘ.comp htsφ).prodMk_nhds hφv
    have h2 := (hsm.continuous.tendsto (θs, v)).comp h1
    refine h2.congr (fun k => ?_)
    simp [Function.comp, (hyu _).2]
  have hzε : ε ≤ Metric.infDist z P.image :=
    ge_of_tendsto ((Metric.continuous_infDist_pt _).continuousAt.tendsto.comp hyz)
      (Eventually.of_forall fun k => htsε (φ k))
  have hvo : v ∈ openUnitDisk := by
    by_contra hvo
    obtain ⟨s, rfl⟩ := rb1_exists_circlePoint hv hvo
    have : z ∈ P.image := ⟨P.T * s, (hbind θs s).symm⟩
    rw [Metric.infDist_zero_of_mem this] at hzε
    linarith
  obtain ⟨ρ, hρ, η, hη, h, hh, c, hc, hcore⟩ :=
    rb1_core H hS page hsm hinj hpS htr hreg y hy Θ u hyu hvo
  have hev1 : ∀ᶠ t in l, ∀ s ∈ Set.Icc t (t + h), |Θ s - θs| < η :=
    hwin _ h hh (by
      filter_upwards [hΘ.eventually (Metric.ball_mem_nhds θs hη)] with s hs
      simpa [Real.dist_eq] using hs)
  have hev2 : ∀ᶠ t in l, |Θ (t + h) - Θ t| < c := by
    have h1 : Tendsto (fun t => Θ (t + h) - Θ t) l (𝓝 (θs - θs)) :=
      (hΘ.comp (hl h)).sub hΘ
    rw [sub_self] at h1
    filter_upwards [h1.eventually (Metric.ball_mem_nhds 0 hc)] with t ht
    simpa [Real.dist_eq] using ht
  have hk : ∀ᶠ k in atTop, ‖y (ts (φ k)) - z‖ < ρ := by
    filter_upwards [hyz.eventually (Metric.ball_mem_nhds z hρ)] with k hk
    simpa [dist_eq_norm] using hk
  obtain ⟨k, hk1, hk2, hk3⟩ := ((htsφ.eventually hev1).and ((htsφ.eventually hev2).and hk)).exists
  have := hcore (ts (φ k)) hk3 hk1
  exact absurd hk2 (not_lt.2 this)

lemma rb1_bddAbove_range {Θ : ℝ → ℝ} (hm : Monotone Θ) {a : ℝ} {B : ℝ}
    (hB : ∀ s ≥ a, Θ s ≤ B) : BddAbove (Set.range Θ) :=
  ⟨B, by rintro _ ⟨x, rfl⟩; exact le_trans (hm (le_max_left x a)) (hB _ (le_max_right _ _))⟩

theorem rb1_main (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (page : ℝ → Plane → R4)
    (hob : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) ∧
      (∀ θ t, page θ (circlePoint t) = P.x (P.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface H, y ∉ P.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u))))
    (y : ℝ → R4) (hy : IsTrajectory H y) (Θ : ℝ → ℝ) (u : ℝ → Plane)
    (hΘ : Continuous Θ) (hmono : StrictMono Θ ∨ StrictAnti Θ)
    (hyu : ∀ t, u t ∈ openUnitDisk ∧ page (Θ t) (u t) = y t) :
    (∀ a : ℝ, Bornology.IsBounded (Θ '' Set.Ici a) →
      Filter.Tendsto (fun t => Metric.infDist (y t) P.image) Filter.atTop (nhds 0)) ∧
    (∀ a : ℝ, Bornology.IsBounded (Θ '' Set.Iic a) →
      Filter.Tendsto (fun t => Metric.infDist (y t) P.image) Filter.atBot (nhds 0)) := by
  obtain ⟨hsm, -, hemb, hpS, hbind, htr, -, hreg⟩ := hob
  have hinj : ∀ θ, Set.InjOn (page θ) closedUnitDisk := fun θ => (hemb θ).2.1
  have hyu' : ∀ t, u t ∈ closedUnitDisk ∧ page (Θ t) (u t) = y t := fun t =>
    ⟨rb1_openUnitDisk_subset (hyu t).1, (hyu t).2⟩
  have key := rb1_end H hS P page hsm hinj hpS hbind htr hreg y hy Θ u hyu'
  constructor
  · intro a hb
    obtain ⟨B, hB⟩ := hb.subset_closedBall 0
    have hB' : ∀ s ≥ a, |Θ s| ≤ B := fun s hs => by
      have := hB ⟨s, hs, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hwin : ∀ (Q : ℝ → Prop) (h : ℝ), 0 < h → (∀ᶠ s in atTop, Q s) →
        ∀ᶠ t in atTop, ∀ s ∈ Set.Icc t (t + h), Q s := by
      intro Q h _ hQ
      obtain ⟨T, hT⟩ := eventually_atTop.1 hQ
      exact eventually_atTop.2 ⟨T, fun t ht s hs => hT s (le_trans ht hs.1)⟩
    have hl : ∀ h : ℝ, Tendsto (fun t => t + h) atTop atTop := fun h =>
      tendsto_atTop_add_const_right _ h tendsto_id
    rcases hmono with hm | hm
    · exact key atTop hl hwin (tendsto_atTop_ciSup hm.monotone
        (rb1_bddAbove_range hm.monotone (fun s hs => (abs_le.1 (hB' s hs)).2)))
    · refine key atTop hl hwin (tendsto_atTop_ciInf hm.antitone ?_)
      have := rb1_bddAbove_range (Θ := fun s => -Θ s) (fun x y hxy => neg_le_neg (hm.antitone hxy))
        (a := a) (B := B) (fun s hs => by linarith [(abs_le.1 (hB' s hs)).1])
      obtain ⟨C, hC⟩ := this
      exact ⟨-C, by rintro _ ⟨x, rfl⟩; linarith [hC ⟨x, rfl⟩]⟩
  · intro a hb
    obtain ⟨B, hB⟩ := hb.subset_closedBall 0
    have hB' : ∀ s ≤ a, |Θ s| ≤ B := fun s hs => by
      have := hB ⟨s, hs, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hwin : ∀ (Q : ℝ → Prop) (h : ℝ), 0 < h → (∀ᶠ s in atBot, Q s) →
        ∀ᶠ t in atBot, ∀ s ∈ Set.Icc t (t + h), Q s := by
      intro Q h _ hQ
      obtain ⟨T, hT⟩ := eventually_atBot.1 hQ
      exact eventually_atBot.2 ⟨T - h, fun t ht s hs => hT s (by linarith [hs.2])⟩
    have hl : ∀ h : ℝ, Tendsto (fun t => t + h) atBot atBot := fun h =>
      tendsto_atBot_add_const_right _ h tendsto_id
    -- reflect time to reuse the bound on `[a, ∞)`
    have hBd : ∀ s ≥ -a, |Θ (-s)| ≤ B := fun s hs => hB' (-s) (by linarith)
    rcases hmono with hm | hm
    · refine key atBot hl hwin (tendsto_atBot_ciInf hm.monotone ?_)
      have := rb1_bddAbove_range (Θ := fun s => -Θ (-s))
        (fun x y hxy => neg_le_neg (hm.monotone (neg_le_neg hxy)))
        (a := -a) (B := B) (fun s hs => by linarith [(abs_le.1 (hBd s hs)).1])
      obtain ⟨C, hC⟩ := this
      exact ⟨-C, by rintro _ ⟨x, rfl⟩; have := hC ⟨-x, rfl⟩; simp only [neg_neg] at this; linarith⟩
    · refine key atBot hl hwin (tendsto_atBot_ciSup hm.antitone ?_)
      have := rb1_bddAbove_range (Θ := fun s => Θ (-s))
        (fun x y hxy => hm.antitone (neg_le_neg hxy))
        (a := -a) (B := B) (fun s hs => (abs_le.1 (hBd s hs)).2)
      obtain ⟨C, hC⟩ := this
      exact ⟨C, by rintro _ ⟨x, rfl⟩; have := hC ⟨-x, rfl⟩; simpa using this⟩

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (page : ℝ → Plane → R4)
    (hob : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2) ∧
      (∀ θ u, page (θ + 1) u = page θ u) ∧
      (∀ θ, IsSmoothDiskEmbedding (page θ)) ∧
      (∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) ∧
      (∀ θ t, page θ (circlePoint t) = P.x (P.T * t)) ∧
      (∀ θ, ∀ u ∈ openUnitDisk,
        hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u)) ∧
      (∀ y ∈ energySurface H, y ∉ P.image →
        ∃! z : ℝ × Plane, z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ openUnitDisk ∧ page z.1 z.2 = y) ∧
      (∀ θ : ℝ, ∀ u ∈ openUnitDisk,
        Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u))))
    (y : ℝ → R4) (hy : IsTrajectory H y) (Θ : ℝ → ℝ) (u : ℝ → Plane)
    (hΘ : Continuous Θ) (hmono : StrictMono Θ ∨ StrictAnti Θ)
    (hyu : ∀ t, u t ∈ openUnitDisk ∧ page (Θ t) (u t) = y t) :
    (∀ a : ℝ, Bornology.IsBounded (Θ '' Set.Ici a) →
      Filter.Tendsto (fun t => Metric.infDist (y t) P.image) Filter.atTop (nhds 0)) ∧
    (∀ a : ℝ, Bornology.IsBounded (Θ '' Set.Iic a) →
      Filter.Tendsto (fun t => Metric.infDist (y t) P.image) Filter.atBot (nhds 0)) :=
  rb1_main H hS P page hob y hy Θ u hΘ hmono hyu
