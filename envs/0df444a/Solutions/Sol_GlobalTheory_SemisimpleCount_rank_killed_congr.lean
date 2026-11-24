-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_killed_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:40.784814+00:00
-- url     : https://prove2.me/submissions/c2b32639-9761-48e6-9cbe-a631e369afe9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_rank_killed_le

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
theorem _root_.solution (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I N) :=
  le_antisymm (rank_killed_le I e.toLinearMap e.injective)
    (rank_killed_le I e.symm.toLinearMap e.symm.injective)
end GlobalTheory.SemisimpleCount
