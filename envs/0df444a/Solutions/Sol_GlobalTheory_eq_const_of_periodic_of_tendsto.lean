-- Prove2me | solution 1 for GlobalTheory.eq_const_of_periodic_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.203726+00:00
-- url     : https://prove2.me/submissions/7dd4f175-2636-466a-a717-6963d8ef42ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {f : ℂ → ℂ} {c : ℂ}
    (hf : DifferentiableOn ℂ f (L.lattice : Set ℂ)ᶜ)
    (hper : ∀ z ∉ L.lattice, ∀ w ∈ L.lattice, f (z + w) = f z)
    (hc : Tendsto f (𝓝[≠] 0) (𝓝 c)) {z : ℂ} (hz : z ∉ L.lattice) : f z = c := by
  classical
  let g : ℂ → ℂ := fun z => if z ∈ L.lattice then c else f z
  have hg : ∀ z, ∀ w ∈ L.lattice, g (z + w) = g z := by
    intro z w hw
    by_cases hz : z ∈ L.lattice
    · simp only [g, if_pos hz, if_pos (add_mem hz hw)]
    · simp only [g, if_neg hz, if_neg (add_notMem_lattice hz hw), hper z hz w hw]
  have hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := by
    intro z hz
    have hn := L.isClosed_lattice.isOpen_compl.mem_nhds hz
    refine (hf.differentiableAt hn).congr_of_eventuallyEq ?_
    filter_upwards [hn] with x hx using if_neg hx
  have h0 : AnalyticAt ℂ g 0 := by
    refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ((eventually_notMem_lattice L 0).mono hd) ?_
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, show g 0 = c from if_pos (zero_mem _)]
    refine hc.congr' ?_
    filter_upwards [eventually_notMem_lattice L 0] with x hx using (if_neg hx).symm
  have hdiff : Differentiable ℂ g := by
    intro x
    by_cases hx : x ∈ L.lattice
    · have e : g = fun z => g (z + -x) := funext fun z => (hg z _ (neg_mem hx)).symm
      rw [e]
      exact DifferentiableAt.comp (g := g) x (by simpa using h0.differentiableAt) (by fun_prop)
    · exact hd x hx
  have := hdiff.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hdiff.continuous hg).isBounded z 0
  simpa only [g, if_neg hz, if_pos (zero_mem L.lattice)] using this
end GlobalTheory
