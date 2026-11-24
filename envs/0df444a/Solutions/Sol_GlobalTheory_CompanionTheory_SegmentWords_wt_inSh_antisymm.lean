-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SegmentWords.wt_inSh_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:00.414127+00:00
-- url     : https://prove2.me/submissions/ea2b1193-0a8a-4e50-ab96-044fb1dfa24f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightAntisymmetricEq
import Theorems.Thm_GlobalTheory_T_shuffle_weight_square_length_lt


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SegmentWords
namespace GlobalTheory.CompanionTheory.SegmentWords
theorem _root_.solution : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) → ∀ (L M : List (ASeg T)), AOrdered s L →
    AOrdered s M → InSh s (M : Multiset (ASeg T)) (wt s L) →
    InSh s (L : Multiset (ASeg T)) (wt s M) →
    (L : Multiset (ASeg T)) = (M : Multiset (ASeg T)) := by
  intro T s hs hj L M hL hM hLM hML
  by_contra hne
  have h1 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj L (M : Multiset (ASeg T)) hL hLM (Ne.symm hne)
  have h2 := GlobalTheory.T.shuffle_weight_square_length_lt s hs hj M (L : Multiset (ASeg T)) hM hML hne
  exact lt_asymm h1 h2
end GlobalTheory.CompanionTheory.SegmentWords
