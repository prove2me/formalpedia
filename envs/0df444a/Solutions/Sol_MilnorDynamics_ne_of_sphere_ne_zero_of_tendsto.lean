-- Prove2me | solution 1 for MilnorDynamics.ne_of_sphere_ne_zero_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:19:58.626973+00:00
-- url     : https://prove2.me/submissions/db23bf00-8e29-409a-8dcc-3527619cd080

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 2 of the minimum-modulus step. The sphere is shown nonempty by
exhibiting the point `z0 + r`, the boundary minimum is taken through the
lambda-form companion of `Continuous.comp_continuousOn`, and the boundedness of
the disc is cited with its `Metric` prefix. -/
theorem solution (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ) (c : ℂ) (g : ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({c}ᶜ : Set ℂ))
    (hc : TendstoLocallyUniformlyOn f g atTop U)
    (z0 : ℂ) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall z0 r ⊆ U)
    (hcirc : ∀ z ∈ Metric.sphere z0 r, g z - c ≠ 0) :
    g z0 ≠ c := by
  intro hg0
  have hsphereU : Metric.sphere z0 r ⊆ U :=
    fun _ hz => hball (Metric.sphere_subset_closedBall hz)
  have hz0U : z0 ∈ U := hball (Metric.mem_closedBall_self hr.le)
  have hgc : ContinuousOn g U :=
    hc.continuousOn (Frequently.of_forall fun n => (hf n).1.continuousOn)
  have hgcs : ContinuousOn (fun z => g z - c) (Metric.sphere z0 r) :=
    (hgc.mono hsphereU).sub continuousOn_const
  have hK : IsCompact (Metric.sphere z0 r) := isCompact_sphere z0 r
  have hne : (Metric.sphere z0 r).Nonempty :=
    ⟨z0 + (r : ℂ), by simp [Metric.mem_sphere, dist_eq_norm, abs_of_pos hr]⟩
  obtain ⟨z1, hz1, hz1min⟩ := hK.exists_isMinOn hne
    (continuous_norm.comp_continuousOn' hgcs)
  set m : ℝ := ‖g z1 - c‖ with hm
  have hmpos : 0 < m := by rw [hm]; exact norm_pos_iff.mpr (hcirc z1 hz1)
  have hmle : ∀ z ∈ Metric.sphere z0 r, m ≤ ‖g z - c‖ := by
    intro z hz
    rw [hm]
    exact hz1min hz
  have hm2pos : (0 : ℝ) < m / 2 := by linarith
  have hev1 : ∀ᶠ n in atTop, ∀ z ∈ Metric.sphere z0 r, dist (g z) (f n z) < m / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hc
        (Metric.sphere z0 r) hsphereU hK)) (m / 2) hm2pos
  have hev2 : ∀ᶠ n in atTop, dist (f n z0) (g z0) < m / 2 :=
    (Metric.tendsto_nhds.mp (hc.tendsto_at hz0U)) (m / 2) hm2pos
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hbd : ∀ z ∈ Metric.sphere z0 r, m / 2 < ‖f n z - c‖ := by
    intro z hz
    have h1 : m ≤ ‖g z - c‖ := hmle z hz
    have h2 : ‖g z - f n z‖ < m / 2 := by simpa [dist_eq_norm] using hn1 z hz
    have h3 : ‖g z - c‖ ≤ ‖g z - f n z‖ + ‖f n z - c‖ := by
      have hsplit : g z - c = (g z - f n z) + (f n z - c) := by ring
      rw [hsplit]
      exact norm_add_le _ _
    linarith
  have hbound : ∀ z ∈ Metric.sphere z0 r, ‖((f n z - c)⁻¹ : ℂ)‖ ≤ (m / 2)⁻¹ := by
    intro z hz
    have hge : m / 2 ≤ ‖f n z - c‖ := le_of_lt (hbd z hz)
    simpa [norm_inv, one_div] using one_div_le_one_div_of_le hm2pos hge
  have hD : DiffContOnCl ℂ (fun z => (f n z - c)⁻¹) (Metric.ball z0 r) := by
    have hsub : closure (Metric.ball z0 r) ⊆ U :=
      Metric.closure_ball_subset_closedBall.trans hball
    have hdiff : DifferentiableOn ℂ (fun z => f n z - c) (closure (Metric.ball z0 r)) :=
      ((hf n).1.sub (differentiableOn_const c)).mono hsub
    have hne' : ∀ z ∈ closure (Metric.ball z0 r), f n z - c ≠ 0 := by
      intro z hz
      exact sub_ne_zero.mpr (by simpa using (hf n).2 (hsub hz))
    exact ⟨(hdiff.inv hne').mono subset_closure, hdiff.continuousOn.inv₀ hne'⟩
  have hMz : ‖((f n z0 - c)⁻¹ : ℂ)‖ ≤ (m / 2)⁻¹ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hD
      (fun z hz => hbound z (Metric.frontier_ball_subset_sphere hz))
      (subset_closure (Metric.mem_ball_self hr))
  have hpos : 0 < ‖f n z0 - c‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (by simpa using (hf n).2 hz0U))
  have hlow : m / 2 ≤ ‖f n z0 - c‖ :=
    (one_div_le_one_div hpos hm2pos).mp (by simpa [norm_inv, one_div] using hMz)
  have hup : ‖f n z0 - c‖ < m / 2 := by simpa [dist_eq_norm, hg0] using hn2
  linarith
