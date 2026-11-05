-- Prove2me | solution 1 for GeneralPieces.TopDisplay.stTopArith2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:11.534341+00:00
-- url     : https://prove2.me/submissions/dd039511-5294-4345-ab14-a974188721a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_kme
import Theorems.Thm_ClauseBound_Alg_TopArith_root9_spec
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution : StTopArith := by
  intro Idx _ S e C₀ Q
  refine ⟨Atop C₀ (max C₀ 2), fun k m hk hm => ?_⟩
  obtain ⟨hr1, hr2⟩ := root9_spec m
  have hK0 : S.K (Q.idx 0) ≤ (root9 m).length := by
    by_contra h
    have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 9
    exact absurd (h'.trans hm) (not_le.2 hr2)
  have hle := Q.pick_le _ hK0
  have hmax := Q.pick_max (root9 m)
  have hidx := Q.pick_idx (root9 m)
  rw [hidx] at hle ⊢
  refine needTop_le_kme S _ _ C₀ k m (max C₀ 2) (Q.e_le _) (Q.K_two _) hk (le_max_right _ _) ((Nat.pow_le_pow_left hle 9).trans hr1) ?_
    (Q.e_ge _) (Q.rate _)
  have h2 := Q.K_two (Q.pick (root9 m)).1.length
  calc m ≤ ((root9 m).length + 1) ^ 9 := hr2.le
    _ ≤ (S.K (Q.idx (Q.pick (root9 m)).1.length) ^ C₀) ^ 9 := Nat.pow_le_pow_left ((Nat.succ_le_of_lt hmax).trans (Q.K_le _)) 9
    _ = S.K (Q.idx (Q.pick (root9 m)).1.length) ^ (9 * C₀) := by rw [← pow_mul, mul_comm]
    _ ≤ S.K (Q.idx (Q.pick (root9 m)).1.length) ^ (9 * max C₀ 2) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (le_max_left _ _))
end GeneralPieces.TopDisplay
