-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_hom_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:39.966529+00:00
-- url     : https://prove2.me/submissions/46bad263-4082-48c4-bec5-af410a167474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_rank_hom_le

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
variable {S : Type} [AddCommGroup S] [Module Rg S]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] N) :=
  le_antisymm (rank_hom_le e.toLinearMap e.injective)
    (rank_hom_le e.symm.toLinearMap e.symm.injective)
end GlobalTheory.SemisimpleCount
