-- Prove2me | solution 1 for GlobalTheory.latticePoint_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:24.695118+00:00
-- url     : https://prove2.me/submissions/bc83565b-1c52-4d95-b911-f9a26b1f79b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair WeierstrassCurve
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
open Filter PeriodPair WeierstrassCurve
open scoped Topology
variable (L : PeriodPair)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {z w : ℂ} :
    _root_.GlobalTheory.latticePoint L z = _root_.GlobalTheory.latticePoint L w ↔ z - w ∈ L.lattice := by
  rw [← _root_.GlobalTheory.latticePoint_eq_zero_iff, sub_eq_add_neg, _root_.GlobalTheory.latticePoint_add,
    _root_.GlobalTheory.latticePoint_neg, ← sub_eq_add_neg, sub_eq_zero]
end _root_.GlobalTheory
end GlobalTheory
