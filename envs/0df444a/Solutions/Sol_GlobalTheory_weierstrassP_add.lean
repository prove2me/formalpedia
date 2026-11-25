-- Prove2me | solution 1 for GlobalTheory.weierstrassP_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:25.570689+00:00
-- url     : https://prove2.me/submissions/e5311ba3-5991-49c9-ab31-310b7bfb1567

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
theorem _root_.solution {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w ∧
    ℘'[L] (z + w) = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) +
      ℘'[L] z) :=
  weierstrassP_add_and_deriv_add_of_ne L hz hw hne
end _root_.GlobalTheory
end GlobalTheory
