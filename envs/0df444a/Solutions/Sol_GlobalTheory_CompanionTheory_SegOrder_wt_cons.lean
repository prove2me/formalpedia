-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SegOrder.wt_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:38:46.21565+00:00
-- url     : https://prove2.me/submissions/dfa398f6-451d-438e-9b87-6c5d9aeb4260

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCommonOrderedForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Zc.Comb
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SegOrder
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.SegOrder
theorem _root_.solution (s : T → T) (a : ASeg T) (L : List (ASeg T)) :
    wt s (a :: L) = wt s L ++ ASeg.dec s a := by
  simp [wt]
end GlobalTheory.CompanionTheory.SegOrder
