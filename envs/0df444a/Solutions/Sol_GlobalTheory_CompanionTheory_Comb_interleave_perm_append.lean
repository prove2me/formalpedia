-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Comb.interleave_perm_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:58.528811+00:00
-- url     : https://prove2.me/submissions/14da6057-291d-4b75-b26c-f16c663e7418

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShufflePermFlatten

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Comb
namespace GlobalTheory.CompanionTheory.Comb
theorem _root_.solution {T : Type u} {u v w : List T} (h : Interleave u v w) :
    w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm
end GlobalTheory.CompanionTheory.Comb
