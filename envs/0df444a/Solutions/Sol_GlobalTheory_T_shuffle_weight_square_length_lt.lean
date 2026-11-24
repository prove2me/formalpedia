-- Prove2me | solution 1 for GlobalTheory.T.shuffle_weight_square_length_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:23.495222+00:00
-- url     : https://prove2.me/submissions/ba7c850a-fe0e-4c15-ad31-561b94f34800

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLtStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_sqLen_lt_of_inSh


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
theorem _root_.solution : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L : List (ASeg T)) (n : Multiset (ASeg T)), AOrdered s L → InSh s n (wt s L) → n ≠ (L : Multiset (ASeg T)) → sqLen n < sqLen (L : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | exact GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh | (intros; apply GlobalTheory.CompanionTheory.MultiSeg.Rank.sqLen_lt_of_inSh <;> assumption)
end _root_.GlobalTheory.T
