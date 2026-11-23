-- Prove2me | solution 1 for GlobalTheory.weierstrass_system_add_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:51.635019+00:00
-- url     : https://prove2.me/submissions/39438036-3fbd-4793-8e85-884b2323f56e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP
import Theorems.Thm_GlobalTheory_hasDerivAt_derivWeierstrassP

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
theorem _root_.solution (c : ℂ) {z : ℂ} (hz : z + c ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, HasDerivAt (fun t ↦ ℘[L] (t + c)) (℘'[L] (w + c)) w ∧
      HasDerivAt (fun t ↦ ℘'[L] (t + c)) (6 * ℘[L] (w + c) ^ 2 - L.g₂ / 2) w := by
  filter_upwards [(continuous_add_const c).continuousAt.eventually
    (eventually_notMem_periodLattice L hz)] with w hw
  exact ⟨(hasDerivAt_weierstrassP L hw).comp_add_const w c,
    (hasDerivAt_derivWeierstrassP L hw).comp_add_const w c⟩
end GlobalTheory
