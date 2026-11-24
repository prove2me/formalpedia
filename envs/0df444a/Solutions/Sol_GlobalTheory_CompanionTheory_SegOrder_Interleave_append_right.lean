-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SegOrder.Interleave.append_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:37.039871+00:00
-- url     : https://prove2.me/submissions/5a997c81-94eb-47e4-b170-1069511bfc30

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOrderedForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCommonOrderedForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SegOrder_interleave_right_nil

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
namespace Interleave
theorem _root_.solution {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave u (v ++ b) (w ++ b) := by
  induction h with
  | nil => exact interleave_right_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih
end Interleave
end GlobalTheory.CompanionTheory.SegOrder
