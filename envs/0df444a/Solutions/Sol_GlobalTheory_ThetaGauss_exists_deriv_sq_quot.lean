-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.exists_deriv_sq_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:44.276477+00:00
-- url     : https://prove2.me/submissions/92bb0571-88e3-430a-800c-53286efa84f4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_entire_quot
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ s, h s ≠ 0)
    (hm : ∀ s, h s = 0 → deriv h s = 0) :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ s, k s * h s = deriv h s ^ 2 := by
  refine exists_entire_quot (hh.deriv.pow 2) hh h0 fun s₀ hs₀ => ?_
  have hnz : ¬ ∀ᶠ s in 𝓝 s₀, h s = 0 := fun hz => by
    obtain ⟨s, hs⟩ := h0
    exact hs ((hh.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ s₀) hz (Set.mem_univ s))
  obtain ⟨n, u, hu, hu0, he⟩ := (hh.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at he
  have hder : ∀ᶠ s in 𝓝 s₀, deriv h s = n * (s - s₀) ^ (n - 1) * u s + (s - s₀) ^ n * deriv u s := by
    filter_upwards [he.eventually_nhds, hu.eventually_analyticAt] with s hs hus
    rw [Filter.EventuallyEq.deriv_eq (f := fun s => (s - s₀) ^ n * u s) hs]
    have := (((hasDerivAt_id s).sub_const s₀).pow n).mul hus.differentiableAt.hasDerivAt
    simpa [Pi.mul_def] using this.deriv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    rcases n with _ | _ | m
    · have := he.self_of_nhds; simp [hs₀] at this; exact absurd this.symm hu0
    · have := hder.self_of_nhds; simp [hm _ hs₀] at this; exact absurd this.symm hu0
    · exact ⟨m, rfl⟩
  let w : ℂ → ℂ := fun s => (s - s₀) ^ m * (((m + 2 : ℕ) : ℂ) * u s + (s - s₀) * deriv u s) ^ 2 / u s
  have hw : ContinuousAt w s₀ := by
    have := hu.continuousAt
    have := hu.deriv.continuousAt
    refine ContinuousAt.div ?_ hu.continuousAt hu0
    fun_prop
  refine ⟨‖w s₀‖ + 1, Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_⟩
  filter_upwards [he, hder, hu.continuousAt.eventually_ne hu0,
    hw.norm.eventually (ge_mem_nhds (lt_add_one _))] with s h1 h2 h3 h4
  have : deriv h s ^ 2 = w s * h s := by
    rw [h1, h2]; simp only [w, show m + 2 - 1 = m + 1 from rfl]; field_simp; ring
  rw [this, norm_mul]
  gcongr
end GlobalTheory.ThetaGauss
