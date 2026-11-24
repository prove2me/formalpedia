-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:38:18.091058+00:00
-- url     : https://prove2.me/submissions/4608aff2-e9ea-40eb-8e59-ca8e9137a946

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShufflePermFlatten
import Theorems.Thm_GlobalTheory_CompanionTheory_Comb_interleave_perm_append

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
theorem _root_.solution {T : Type u} (us : List (List T)) (w : List T)
    (h : Shuffle us w) : w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih =>
    rw [List.flatten_cons]
    exact (interleave_perm_append hi).trans (ih.append_left _)
end GlobalTheory.CompanionTheory.Comb
