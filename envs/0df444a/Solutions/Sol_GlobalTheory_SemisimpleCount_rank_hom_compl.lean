-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_hom_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:11:01.055276+00:00
-- url     : https://prove2.me/submissions/f8201d4f-4db1-490c-beac-fec72089b6a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_rank_hom_congr

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
theorem _root_.solution {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] U) + Module.rank ℂ (S →ₗ[Rg] V) := by
  rw [← rank_hom_congr (Submodule.prodEquivOfIsCompl U V h), ← rank_prod']
  exact (LinearMap.prodEquiv ℂ).rank_eq.symm
end GlobalTheory.SemisimpleCount
