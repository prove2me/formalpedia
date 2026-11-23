-- Prove2me | solution 1 for GlobalTheory.eq_of_differentiable_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:12.575019+00:00
-- url     : https://prove2.me/submissions/ce43f94a-dc56-4d96-b578-19b6df0e7feb

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
theorem _root_.solution {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hp : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) (z w : ℂ) : f z = f w :=
  hf.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hf.continuous hp).isBounded z w
end GlobalTheory
