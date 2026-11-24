-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.exists_ne_zero_of_rank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:44:32.910188+00:00
-- url     : https://prove2.me/submissions/1a0d6c72-0ccb-4f37-a4cf-698a16616e3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq

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
theorem _root_.solution {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (h : Module.rank ℂ A = Module.rank ℂ B) {a : A} (ha : a ≠ 0) :
    ∃ b : B, b ≠ 0 := by
  by_contra hb
  push_neg at hb
  exact ha (rank_zero_iff_forall_zero.1 (h.trans (rank_zero_iff_forall_zero.2 hb)) a)
end GlobalTheory.SemisimpleCount
