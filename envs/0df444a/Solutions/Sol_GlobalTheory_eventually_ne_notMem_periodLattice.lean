-- Prove2me | solution 1 for GlobalTheory.eventually_ne_notMem_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:40.305374+00:00
-- url     : https://prove2.me/submissions/32088205-e901-428d-831f-1ba9e2ac7ec5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero

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
theorem _root_.solution (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds z)] with w hw hw'
  simp_all
end GlobalTheory
