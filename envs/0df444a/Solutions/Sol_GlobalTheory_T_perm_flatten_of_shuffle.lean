-- Prove2me | solution 1 for GlobalTheory.T.perm_flatten_of_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:07.733139+00:00
-- url     : https://prove2.me/submissions/ec9ba044-2d74-4fd4-b3d3-9dfb864f839f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShufflePermFlatten
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShufflePermFlattenStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Comb_shuffle_perm_flatten


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {T : Type u} (us : List (List T)) (w : List T), Shuffle us w → w.Perm us.flatten := by
  first | exact @GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten | exact GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten | (intros; apply GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten <;> assumption)
end _root_.GlobalTheory.T
