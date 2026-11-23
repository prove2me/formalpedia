-- Prove2me | solution 1 for GlobalTheory.sub_mem_lattice_of_weierstrassP_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:15.135588+00:00
-- url     : https://prove2.me/submissions/2accd379-788b-4651-9f50-2fe20f70523e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_eqOn_compl_of_countable
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_not_eventually_weierstrassP_eq
import Theorems.Thm_GlobalTheory_eventuallyEq_of_weierstrass_system
import Theorems.Thm_GlobalTheory_weierstrass_system_add_const
import Theorems.Thm_GlobalTheory_countable_add_mem_periodLattice
import Theorems.Thm_GlobalTheory_analyticAt_weierstrassP_add

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
theorem _root_.solution {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : ℘[L] z = ℘[L] w) (h' : ℘'[L] z = ℘'[L] w) : z - w ∈ L.lattice := by
  by_contra hc
  have hw' : w + (z - w) ∉ L.lattice := by simpa using hz
  have h1 := eventuallyEq_of_weierstrass_system
    (weierstrass_system_add_const L 0 (z := w) (by simpa using hw))
    (weierstrass_system_add_const L (z - w) hw') (by simp [h]) (by simp [h'])
  have h2 := eqOn_compl_of_countable
    ((countable_add_mem_periodLattice L 0).union (countable_add_mem_periodLattice L (z - w)))
    (fun t ht ↦ analyticAt_weierstrassP_add L 0 fun h ↦ ht (.inl h))
    (fun t ht ↦ analyticAt_weierstrassP_add L (z - w) fun h ↦ ht (.inr h))
    (z := w) (by rintro (h | h); exacts [hw (by simpa using h), hw' h]) h1
  have h0 : 0 + (z - w) ∉ L.lattice := by simpa using hc
  refine not_eventually_weierstrassP_eq L (zero_mem _)
    (analyticAt_weierstrassP_add L (z - w) h0).continuousAt ?_
  filter_upwards [eventually_ne_notMem_periodLattice L 0, mem_nhdsWithin_of_mem_nhds
    ((continuous_add_const (z - w)).continuousAt.eventually
      (eventually_notMem_periodLattice L h0))] with t h3 h4
  simpa using h2 (x := t) (by rintro (h | h); exacts [h3 (by simpa using h), h4 h])
end GlobalTheory
