-- Prove2me | solution 1 for GlobalTheory.sum_min_succ_eq_add_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:07.053516+00:00
-- url     : https://prove2.me/submissions/3e0f2a75-a2c7-45b6-94c6-bb090d122f83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    ∑ i, min (j + 1) (e i) = ∑ i, min j (e i) + (Finset.univ.filter (fun i => j < e i)).card := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega
end GlobalTheory
