-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ShuffleWords.shuffle_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:16.921508+00:00
-- url     : https://prove2.me/submissions/67a9e7eb-ff5e-4629-a51a-33a7ea570cfa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleOfPerm
import Theorems.Thm_GlobalTheory_CompanionTheory_ShuffleWords_interleave_exchange

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
theorem _root_.solution {a b : List T} {us : List (List T)} {w : List T}
    (h : Shuffle (a :: b :: us) w) : Shuffle (b :: a :: us) w := by
  cases h with
  | cons hv hw =>
    cases hv with
    | cons hx hv =>
      obtain ⟨v', h₁, h₂⟩ := interleave_exchange hw hv
      exact Shuffle.cons (Shuffle.cons hx h₂) h₁
end GlobalTheory.CompanionTheory.ShuffleWords
