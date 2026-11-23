-- Prove2me | solution 1 for GlobalTheory.countable_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:40.224878+00:00
-- url     : https://prove2.me/submissions/9580bd78-2355-4c34-b963-7ef397b8ec4d

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
theorem _root_.solution : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)
end GlobalTheory
