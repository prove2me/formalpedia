-- Prove2me | solution 1 for GlobalTheory.countable_add_mem_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:56.348097+00:00
-- url     : https://prove2.me/submissions/4847dd81-1a62-4a11-8e55-bd1896605acc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_countable_periodLattice

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
theorem _root_.solution (c : ℂ) : {z : ℂ | z + c ∈ L.lattice}.Countable :=
  (countable_periodLattice L).preimage_of_injOn (f := (· + c)) (add_left_injective c).injOn
end GlobalTheory
