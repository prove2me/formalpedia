-- Prove2me | solution 1 for GlobalTheory.JetConj.eventually_add_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:47.123585+00:00
-- url     : https://prove2.me/submissions/958143d2-d9e2-4d26-baaf-2d1f6862b1f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}
namespace GlobalTheory.JetConj
theorem _root_.solution (L : PeriodPair) {u z : ℂ} (hz : z + u ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w + u ∉ L.lattice :=
  (continuous_add_const u).continuousAt.eventually (eventually_notMem_periodLattice L hz)
end GlobalTheory.JetConj
