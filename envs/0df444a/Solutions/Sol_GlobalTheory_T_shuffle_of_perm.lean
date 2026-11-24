-- Prove2me | solution 1 for GlobalTheory.T.shuffle_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:22.804465+00:00
-- url     : https://prove2.me/submissions/304d12f1-097c-4780-b9fd-f3d6dbde92f9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleOfPerm
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleOfPermStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ShuffleWords_shuffle_perm


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
theorem _root_.solution : ∀ {T : Type u} (us us' : List (List T)) (w : List T), Shuffle us w → us.Perm us' → Shuffle us' w := by
  first | exact @GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | exact GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | (intros; apply GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm <;> assumption)
end _root_.GlobalTheory.T
