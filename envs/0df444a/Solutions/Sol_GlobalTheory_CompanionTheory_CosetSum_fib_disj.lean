-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetSum.fib_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:42.645294+00:00
-- url     : https://prove2.me/submissions/7a6fb595-b6d6-4088-98d1-fb91aacd3aeb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetIntegralUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetSum
variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
namespace GlobalTheory.CompanionTheory.CosetSum
theorem _root_.solution (H : AddSubgroup G) : Pairwise (Function.onFun Disjoint (fib H)) :=
  fun _ _ hcd => (Set.disjoint_singleton.mpr hcd).preimage _
end GlobalTheory.CompanionTheory.CosetSum
