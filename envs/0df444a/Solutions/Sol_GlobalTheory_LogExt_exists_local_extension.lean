-- Prove2me | solution 1 for GlobalTheory.LogExt.exists_local_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:13.926281+00:00
-- url     : https://prove2.me/submissions/29405b58-32e2-42d8-b5b4-bb86e918305b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth
import Theorems.Thm_GlobalTheory_LogExt_cauchy_of_log_growth
import Theorems.Thm_GlobalTheory_LogExt_analyticOnNhd_of_differentiableOn
import Theorems.Thm_GlobalTheory_LogExt_differentiableAt_lineIntegral
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.LogExt
theorem _root_.solution [FiniteDimensional ℂ V] {U : Set V} {φ u : V → ℂ} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hu : DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0})
    (hd : U ⊆ closure {b ∈ U | φ b ≠ 0})
    (hb : ∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) {b₀ : V} (hb₀ : b₀ ∈ U) :
    ∃ w : V → ℂ, ∀ᶠ b in 𝓝 b₀, DifferentiableAt ℂ w b ∧ (φ b ≠ 0 → w b = u b) := by
  have hΩ : IsOpen {b ∈ U | φ b ≠ 0} :=
    hφ.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hφa := analyticOnNhd_of_differentiableOn hU hφ
  have hua := analyticOnNhd_of_differentiableOn hΩ hu
  have hline : ∀ (b v : V) (t : ℂ), AnalyticAt ℂ (fun s : ℂ => b + s • v) t := fun b v t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hgan : ∀ (b v : V) (t : ℂ), b + t • v ∈ U → AnalyticAt ℂ (fun s : ℂ => φ (b + s • v)) t :=
    fun b v t h => AnalyticAt.comp (f := fun s : ℂ => b + s • v) (hφa _ h) (hline b v t)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU b₀ hb₀
  obtain ⟨b₁, hb₁, hb₁r⟩ := Metric.mem_closure_iff.mp (hd hb₀) r hr
  set v := b₁ - b₀ with hv
  have hvr : ‖v‖ < r := by rwa [dist_comm, dist_eq_norm] at hb₁r
  have hin : ∀ t ∈ closedBall (0 : ℂ) 1, b₀ + t • v ∈ U := fun t ht => by
    refine hrU ?_
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans_lt hvr
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => φ (b₀ + s • v)) (closedBall 0 1) :=
    fun t ht => hgan _ _ _ (hin t ht)
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), φ (b₀ + z • v) = 0 := fun h => by
    have := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall (0 : ℂ) 1).isPreconnected (mem_closedBall_self zero_le_one) h
      (show (1 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp)
    exact hb₁.2 (by simpa [hv] using this)
  have hev := (hg 0 (mem_closedBall_self zero_le_one)).eventually_eq_zero_or_eventually_ne_zero.resolve_left hne
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hev
  set R := min ε 1 with hR
  have hR0 : 0 < R := lt_min hε one_pos
  have hc : ∀ t : ℂ, ContinuousAt (fun p : V × ℂ => p.1 + p.2 • v) (b₀, t) := fun t => by fun_prop
  have h1 : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ closedBall (0 : ℂ) R, b + t • v ∈ U :=
    (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht =>
      (hc t).eventually (hU.mem_nhds (hin t (closedBall_subset_closedBall (min_le_right _ _) ht)))
  have h2 : ∀ᶠ b in 𝓝 b₀, ∀ t ∈ sphere (0 : ℂ) R, b + t • v ∈ {b ∈ U | φ b ≠ 0} :=
    (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually fun t ht =>
      (hc t).eventually (hΩ.mem_nhds ⟨hin t (closedBall_subset_closedBall (min_le_right _ _)
        (sphere_subset_closedBall ht)), hεs (closedBall_subset_closedBall (min_le_left _ _)
        (sphere_subset_closedBall ht)) (ne_of_mem_sphere ht hR0.ne')⟩)
  refine ⟨fun b => (2 * π * I : ℂ)⁻¹ • ∮ t in C(0, R), t⁻¹ • u (b + t • v), ?_⟩
  filter_upwards [h1, h2] with b hb1 hb2
  refine ⟨(differentiableAt_lineIntegral hua hR0 hb2).fun_const_smul _, fun hφb => ?_⟩
  have := cauchy_of_log_growth (f := fun s : ℂ => u (b + s • v)) (g := fun s : ℂ => φ (b + s • v)) hR0
    (fun t ht => hgan _ _ _ (hb1 t ht)) (by simpa using hφb) (fun t ht => (hb2 t ht).2)
    (fun t ht => by
      filter_upwards [(hline b v t).continuousAt.eventually (hU.mem_nhds (hb1 t ht))] with z hz hz0
      exact (AnalyticAt.comp (f := fun s : ℂ => b + s • v) (hua _ ⟨hz, hz0⟩)
        (hline b v z)).differentiableAt)
    (fun t ht => by
      obtain ⟨C, k, h⟩ := hb _ (hb1 t ht)
      exact ⟨C, k, (hline b v t).continuousAt.eventually h⟩)
  simp only [this, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul, zero_smul, add_zero]
end GlobalTheory.LogExt
