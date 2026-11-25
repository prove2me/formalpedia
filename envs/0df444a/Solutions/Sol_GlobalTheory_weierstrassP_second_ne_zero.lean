-- Prove2me | solution 1 for GlobalTheory.weierstrassP_second_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:31.173175+00:00
-- url     : https://prove2.me/submissions/ff2277ad-35b0-4bd8-bdd8-42013ca4de43

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
theorem _root_.solution {w : ℂ} (hw : w ∉ L.lattice)
    (h : ℘'[L] w = 0) : 6 * ℘[L] w ^ 2 - L.g₂ / 2 ≠ 0 := by
  intro h6
  have ew := derivWeierstrassP_sq L w hw
  rw [h] at ew
  have hΔ := _root_.GlobalTheory.latticeCurve_Δ_ne_zero L
  rw [_root_.GlobalTheory.latticeCurve_Δ] at hΔ
  apply hΔ
  have hg2 : L.g₂ = 12 * ℘[L] w ^ 2 := by linear_combination -2 * h6
  have hg3 : L.g₃ = -8 * ℘[L] w ^ 3 := by linear_combination ew + 2 * ℘[L] w * h6
  rw [hg2, hg3]
  ring
end _root_.GlobalTheory
end GlobalTheory
