-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.bound_on_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:47.240157+00:00
-- url     : https://prove2.me/submissions/0c15e6c8-1391-4062-95cc-22cab4e04a3c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_norm_deriv_sq_le
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_differentiable_transl
import Theorems.Thm_GlobalTheory_ThetaGauss_hasDerivAt_line
import Theorems.Thm_GlobalTheory_ThetaGauss_not_eventually_zero
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_sphere
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (v : Fin g → ℂ)
    (hm : ∀ a, θ a = 0 → fderiv ℂ θ a v = 0) (z w : Fin g → ℂ) (h0 : ∃ s : ℂ, θ (z + s • w) ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖fderiv ℂ θ (z + s • w) v ^ 2‖ ≤ C * ‖θ (z + s • w)‖ := by
  let K : Set ℂ := closedBall 0 1
  let γ : C(K, Fin g → ℂ) := ⟨fun t => (t : ℂ) • v, by fun_prop⟩
  let Φ : ℂ → C(K, ℂ) := fun s => transl hθ γ (z + s • w)
  have hΦ : Differentiable ℂ Φ := (differentiable_transl hθ γ).comp (by fun_prop)
  have hnz : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), Φ s = 0 := fun hz =>
    not_eventually_zero (h := fun s => θ (z + s • w)) (by fun_prop) h0 0 (hz.mono fun s hs => by
      simpa [Φ, γ] using congrArg (fun F : C(K, ℂ) => F ⟨0, by simp [K]⟩) hs)
  obtain ⟨n, G, hG, hG0, he⟩ := (hΦ.analyticAt 0).exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [sub_zero] at he
  let F : ℂ → ℂ → ℂ := fun s t => (s ^ n)⁻¹ * θ (z + s • w + t • v)
  have hFd : ∀ s, Differentiable ℂ (F s) := fun s => by fun_prop
  have hF : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ t : K, F s t = G s t := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0 t
    have := congrArg (fun F : C(K, ℂ) => F t) hs
    simp only [Φ, γ, transl_apply, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul] at this
    simp only [F]
    rw [this, inv_mul_cancel_left₀ (pow_ne_zero _ hs0)]
  have hclose : ∀ ε > 0, ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ t : K, ‖F s t - G 0 t‖ < ε := fun ε hε => by
    filter_upwards [hF, ((Metric.tendsto_nhds.1 hG.continuousAt) ε hε).filter_mono
      nhdsWithin_le_nhds] with s hs hs' t
    rw [hs, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt hs'
  classical
  let g₀ : ℂ → ℂ := fun t => if h : t ∈ K then G 0 ⟨t, h⟩ else 0
  have hg₀ : ∀ t : K, g₀ t = G 0 t := fun t => by simp [g₀]
  have hu : TendstoUniformlyOn F g₀ (𝓝[≠] 0) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hclose ε hε] with s hs t ht
    rw [dist_comm, dist_eq_norm, hg₀ ⟨t, ht⟩]
    exact hs ⟨t, ht⟩
  have hgd : DifferentiableOn ℂ g₀ (ball 0 1) :=
    (hu.mono ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun s => (hFd s).differentiableOn) isOpen_ball
  have hgc : ContinuousOn g₀ K :=
    hu.continuousOn (Eventually.of_forall fun s => (hFd s).continuous.continuousOn).frequently
  have hga := hgd.analyticOnNhd isOpen_ball
  have hgne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g₀ t ≠ 0 := by
    refine (hga 0 (by simp)).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz => hG0 ?_
    have h1 := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected
      (mem_ball_self one_pos) hz
    have h2 : Set.EqOn g₀ 0 K := h1.of_subset_closure hgc continuousOn_const
      ball_subset_closedBall (by rw [closure_ball _ one_ne_zero])
    ext t
    rw [← hg₀]; exact h2 t.2
  obtain ⟨r, hr, hr', hsph⟩ := exists_sphere hgne
  have hsub : sphere (0 : ℂ) r ⊆ K := sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) (hgc.mono hsub).norm
  have hδ : 0 < ‖g₀ t₀‖ / 2 := half_pos (norm_pos_iff.2 (hsph t₀ ht₀))
  refine ⟨(2 * (‖G 0‖ + 1)) ^ 2 / (‖g₀ t₀‖ / 2), ?_⟩
  filter_upwards [hclose _ hδ, hclose 1 one_pos, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (closedBall_mem_nhds (0 : ℂ) one_pos)] with s h1 h2 hs0 hs1
  have hsn : s ^ n ≠ 0 := pow_ne_zero _ hs0
  have hder : ∀ t, deriv (F s) t = (s ^ n)⁻¹ * fderiv ℂ θ (z + s • w + t • v) v := fun t =>
    ((hasDerivAt_line hθ (z + s • w) v t).const_mul _).deriv
  have key := norm_deriv_sq_le (hFd s) (fun t ht => by
      rw [hder, hm _ ((mul_eq_zero.1 ht).resolve_left (inv_ne_zero hsn)), mul_zero])
    hr hr' hδ (M := ‖G 0‖ + 1) (fun t ht => by
      have := h2 ⟨t, ht⟩
      linarith [norm_sub_norm_le (F s t) (G 0 ⟨t, ht⟩), (G 0).norm_coe_le_norm ⟨t, ht⟩])
    (fun t ht => by
      have h3 := h1 ⟨t, hsub ht⟩
      have h4 : ‖g₀ t₀‖ ≤ ‖g₀ t‖ := hmin ht
      rw [← hg₀, norm_sub_rev] at h3
      linarith [norm_sub_norm_le (g₀ t) (F s t)])
  rw [hder] at key
  simp only [F, zero_smul, add_zero, mul_pow, norm_mul] at key
  rw [← mul_pow] at key
  set C := (2 * (‖G 0‖ + 1)) ^ 2 / (‖g₀ t₀‖ / 2)
  have hC : 0 ≤ C := by positivity
  have hle : ‖s ^ n‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (by simpa using hs1)
  have hpos : 0 < ‖s ^ n‖ := norm_pos_iff.2 hsn
  rw [norm_pow, norm_inv] at key
  calc _ = ‖s ^ n‖ ^ 2 * (‖s ^ n‖⁻¹ ^ 2 * ‖fderiv ℂ θ (z + s • w) v ^ 2‖) := by field_simp
    _ ≤ ‖s ^ n‖ ^ 2 * (C * (‖s ^ n‖⁻¹ * ‖θ (z + s • w)‖)) := by gcongr
    _ = ‖s ^ n‖ * (C * ‖θ (z + s • w)‖) := by field_simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hle
end GlobalTheory.ThetaGauss
