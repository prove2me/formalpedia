-- Prove2me | solution 1 for GlobalTheory.JetConj.wr_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:25:56.157052+00:00
-- url     : https://prove2.me/submissions/413e9751-4c7d-4c3f-a97b-10c5f06ac192

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
namespace GlobalTheory.JetConj
theorem _root_.solution {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : wr f z = wr g z := by
  unfold wr
  rw [h.eq_of_nhds, h.deriv.eq_of_nhds, h.deriv.deriv.eq_of_nhds]
end GlobalTheory.JetConj
