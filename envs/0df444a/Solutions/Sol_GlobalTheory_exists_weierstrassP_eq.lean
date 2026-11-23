-- Prove2me | solution 1 for GlobalTheory.exists_weierstrassP_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:03.008359+00:00
-- url     : https://prove2.me/submissions/3b11ccd0-f8c9-4e5a-bf94-52db4af4f864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_tendsto_weierstrassP_cobounded
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP
import Theorems.Thm_GlobalTheory_eq_of_differentiable_of_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution (c : ℂ) : ∃ z ∉ L.lattice, ℘[L] z = c := by
  classical
  by_contra! hc
  let f : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else (℘[L] z - c)⁻¹
  have hf1 : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z := fun z hz ↦ by
    refine (((hasDerivAt_weierstrassP L hz).differentiableAt.sub_const c).inv
      (sub_ne_zero.mpr (hc z hz))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_notMem_periodLattice L hz] with w hw
    simp [f, hw]
  have hf : Differentiable ℂ f := fun z ↦ by
    by_cases hz : z ∈ L.lattice
    · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        ((eventually_ne_notMem_periodLattice L z).mono hf1) ?_).differentiableAt
      rw [continuousAt_iff_punctured_nhds, show f z = 0 by simp [f, hz]]
      refine (tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded c).comp
        (tendsto_weierstrassP_cobounded L hz))).congr' ?_
      filter_upwards [eventually_ne_notMem_periodLattice L z] with w hw
      simp [f, hw]
    · exact hf1 z hz
  have := eq_of_differentiable_of_periodic L hf (fun z l hl ↦ by
    simp only [f, L.weierstrassP_add_coe z ⟨l, hl⟩, (L.lattice.add_mem_iff_left hl)])
    (L.ω₁ / 2) 0
  simp [f, L.ω₁_div_two_notMem_lattice, sub_ne_zero.mpr (hc _ L.ω₁_div_two_notMem_lattice)] at this
end GlobalTheory
