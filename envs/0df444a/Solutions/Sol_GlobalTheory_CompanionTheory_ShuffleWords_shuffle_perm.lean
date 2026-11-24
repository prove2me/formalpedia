-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:17:00.246256+00:00
-- url     : https://prove2.me/submissions/48252018-a17c-4362-82fa-6c982e4c16b7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleOfPerm
import Theorems.Thm_GlobalTheory_CompanionTheory_ShuffleWords_shuffle_swap

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ShuffleWords
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.ShuffleWords
theorem _root_.solution {T : Type u} (us us' : List (List T)) (w : List T)
    (h : Shuffle us w) (hp : us.Perm us') : Shuffle us' w := by
  induction hp generalizing w with
  | nil => exact h
  | cons a _ ih =>
    cases h with
    | cons hv hw => exact Shuffle.cons (ih _ hv) hw
  | swap a b l => exact shuffle_swap h
  | trans _ _ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)
end GlobalTheory.CompanionTheory.ShuffleWords
