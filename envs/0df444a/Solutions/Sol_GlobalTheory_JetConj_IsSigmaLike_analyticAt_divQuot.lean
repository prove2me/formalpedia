-- Prove2me | solution 1 for GlobalTheory.JetConj.IsSigmaLike.analyticAt_divQuot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:46.851378+00:00
-- url     : https://prove2.me/submissions/a4653fe4-0f5f-48e0-84a1-2b6a1d330f4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero

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
namespace IsSigmaLike
theorem _root_.solution (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    AnalyticAt ℂ (divQuot σ u n) z := by
  have hσ := H.diff
  have a : Differentiable ℂ fun z => σ (n * z + n * u) := by fun_prop
  have b : Differentiable ℂ fun z => σ (z + u) ^ (n ^ 2) := by fun_prop
  exact (a.analyticAt z).fun_div (b.analyticAt z) (pow_ne_zero _ (mt (H.zero_iff _).1 hz))
end IsSigmaLike
end GlobalTheory.JetConj
