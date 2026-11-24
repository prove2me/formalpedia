-- Prove2me | solution 1 for GlobalTheory.T.shuffle_weight_antisymmetric_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:08.434168+00:00
-- url     : https://prove2.me/submissions/7b4d87bf-f7f5-4f45-b8dd-feef1f013825

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightAntisymmetricEq
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightAntisymmetricEqStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SegmentWords_wt_inSh_antisymm


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
theorem _root_.solution : ∀ {T : Type u} (s : T → T), Function.Injective s → (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L → AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) → InSh s (L : Multiset (ASeg T)) (wt s M) → (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  first | exact @GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | exact GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm | (intros; apply GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm <;> assumption)
end _root_.GlobalTheory.T
