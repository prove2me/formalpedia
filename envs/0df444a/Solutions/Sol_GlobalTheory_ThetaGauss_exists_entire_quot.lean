-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.exists_entire_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:10.704216+00:00
-- url     : https://prove2.me/submissions/11f58ffe-90f0-4237-b92f-daa8dfe88ac9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
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
theorem _root_.solution {N h : ℂ → ℂ} (hN : Differentiable ℂ N) (hh : Differentiable ℂ h)
    (h0 : ∃ s, h s ≠ 0)
    (hb : ∀ s₀, h s₀ = 0 → ∃ C : ℝ, ∀ᶠ s in 𝓝[≠] s₀, ‖N s‖ ≤ C * ‖h s‖) :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ s, k s * h s = N s := by
  have hne : ∀ s₀, ∀ᶠ s in 𝓝[≠] s₀, h s ≠ 0 := fun s₀ => by
    refine (hh.analyticAt s₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz => ?_
    obtain ⟨s, hs⟩ := h0
    exact hs ((hh.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ s₀) hz (Set.mem_univ s))
  let q : ℂ → ℂ := fun s => N s / h s
  have hq : ∀ s, h s ≠ 0 → DifferentiableAt ℂ q s := fun s hs => (hN s).div (hh s) hs
  let k : ℂ → ℂ := fun s => limUnder (𝓝[≠] s) q
  have hk : ∀ s, h s ≠ 0 → k s = q s := fun s hs =>
    ((hq s hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hd : Differentiable ℂ k := by
    intro s₀
    by_cases hs : h s₀ = 0
    · obtain ⟨C, hC⟩ := hb s₀ hs
      obtain ⟨U, hU, hU'⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hC.and (hne s₀))
      have h1 : DifferentiableOn ℂ (Function.update q s₀ (limUnder (𝓝[≠] s₀) q)) U := by
        refine Complex.differentiableOn_update_limUnder_of_bddAbove hU
          (fun s hs => (hq s (hU' ⟨hs.1, hs.2⟩).2).differentiableWithinAt) ⟨C, ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        have := hU' ⟨hs.1, hs.2⟩
        simp only [Function.comp, q, norm_div]
        rw [div_le_iff₀ (norm_pos_iff.2 this.2)]
        exact this.1
      refine (h1.differentiableAt hU).congr_of_eventuallyEq ?_
      filter_upwards [hU] with s hs
      by_cases e : s = s₀
      · subst e; simp [k]
      · rw [Function.update_of_ne e, hk s (hU' ⟨hs, e⟩).2]
    · refine (hq s₀ hs).congr_of_eventuallyEq ?_
      filter_upwards [(hh s₀).continuousAt.eventually_ne hs] with s hs using hk s hs
  refine ⟨k, hd, fun s₀ => ?_⟩
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s₀)
    (((hd s₀).mul (hh s₀)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hN s₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [hne s₀] with s hs
  simp only [Pi.mul_apply]
  rw [hk s hs, div_mul_cancel₀ _ hs]
end GlobalTheory.ThetaGauss
