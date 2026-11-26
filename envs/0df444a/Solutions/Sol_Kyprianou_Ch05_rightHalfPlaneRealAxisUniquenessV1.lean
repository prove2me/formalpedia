-- Prove2me | solution 1 for Kyprianou.Ch05.rightHalfPlaneRealAxisUniquenessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:54:49.797563+00:00
-- url     : https://prove2.me/submissions/04aecb48-6182-46c5-b59d-376994f1ea20

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set Complex Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (f g : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f {z : ℂ | 0 < z.re})
    (hg : DiffContOnCl ℂ g {z : ℂ | 0 < z.re})
    (hreal : ∀ x : ℝ, 0 < x → f (x : ℂ) = g (x : ℂ)) :
    ∀ z : ℂ, 0 ≤ z.re → f z = g z := by
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU : IsPreconnected {z : ℂ | 0 < z.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have ht : Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_,?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ne_of_gt ht
  have he : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), f (t : ℂ) = g (t : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t (zero_lt_one.trans ht)
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), f z = g z := ht.frequently he.frequently
  have ha := hf.differentiableOn.analyticOnNhd ho
  have hb := hg.differentiableOn.analyticOnNhd ho
  have hEq := ha.eqOn_of_preconnected_of_frequently_eq hb hU h1 hfreq
  have hclosed := hEq.of_subset_closure hf.continuousOn hg.continuousOn subset_closure subset_rfl
  intro z hz
  apply hclosed
  rwa [Complex.closure_setOfPred_lt_re]
