-- Prove2me | solution 1 for GlobalTheory.meromorphic_weierstrassZeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:15.25649+00:00
-- url     : https://prove2.me/submissions/7979969c-544d-484d-bc59-70fb279a460e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_analyticOnNhd_weierstrassZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution : Meromorphic (weierstrassZeta L) := by
  intro x
  by_cases hx : x ∈ L.lattice
  · have e : weierstrassZeta L =
        fun z => weierstrassZetaExcept L x z + (1 / (z - x) + 1 / x + z / x ^ 2) := by
      ext z; rw [← weierstrassZetaExcept_add L hx, zetaTerm_eq]
    have := (analyticAt_weierstrassZetaExcept L x).meromorphicAt
    rw [e]
    fun_prop
  · exact (analyticOnNhd_weierstrassZeta L x hx).meromorphicAt
end GlobalTheory
