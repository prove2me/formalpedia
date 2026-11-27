-- Prove2me | solution 1 for GlobalTheory.JacobiTriple.QBinomial.qPoch_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:36:31.340516+00:00
-- url     : https://prove2.me/submissions/3e57c777-71bd-4a92-be86-7e8363334f1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
open GlobalTheory GlobalTheory.JacobiTriple GlobalTheory.JacobiTriple.QBinomial
open GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple.QBinomial
theorem _root_.solution (t : ℂ) (n : ℕ) : qPoch t (n + 1) = qPoch t n * (1 - t ^ (n + 1)) := by
  unfold qPoch; rw [Finset.prod_range_succ]
end GlobalTheory.JacobiTriple.QBinomial
