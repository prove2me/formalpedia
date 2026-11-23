-- Prove2me | solution 1 for GlobalTheory.eventually_notMem_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:39.374807+00:00
-- url     : https://prove2.me/submissions/76ff029c-4410-49f3-a438-e97957ba502c

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
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w ∉ L.lattice :=
  L.isClosed_lattice.isOpen_compl.mem_nhds hz
end GlobalTheory
