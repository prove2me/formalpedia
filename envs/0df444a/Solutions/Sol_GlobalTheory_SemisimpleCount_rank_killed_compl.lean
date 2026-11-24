-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_killed_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:44.444724+00:00
-- url     : https://prove2.me/submissions/dcd49e7d-ad03-4c02-82d5-2c2bc387df42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_rank_killed_congr
import Theorems.Thm_GlobalTheory_SemisimpleCount_rank_killed_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I U) + Module.rank ℂ (killed I V) := by
  rw [← rank_killed_congr I (Submodule.prodEquivOfIsCompl U V h), rank_killed_prod]
end GlobalTheory.SemisimpleCount
