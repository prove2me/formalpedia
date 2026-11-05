-- Prove2me | solution 1 for GeneralPieces.TopDisplay.sq_L_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:35.510967+00:00
-- url     : https://prove2.me/submissions/f660a916-2f1b-4efd-8f7f-8438fd11ee65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
variable {K k m : ℕ}
namespace GeneralPieces.TopDisplay
theorem _root_.solution (hK : 2 ≤ K) : (K : ℝ) ^ 2 * lamTopK K (3 * K ^ 8) k m ≤
    (K : ℝ) ^ 2 + 2 * k * m + ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) / K := by
  have hκ : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hd : lamTopK K (3 * K ^ 8) k m * K ^ 3 ≤ K ^ 3 + K * (2 * k * m) + 3 * K ^ 8 * PtopK (3 * K ^ 8) k m := Nat.div_mul_le_self _ _
  have hd' : (lamTopK K (3 * K ^ 8) k m : ℝ) * (K : ℝ) ^ 3 ≤ (K : ℝ) ^ 3 + K * (2 * k * m) + ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) := by
    exact_mod_cast hd
  generalize ((3 * K ^ 8 * PtopK (3 * K ^ 8) k m : ℕ) : ℝ) = G at hd' ⊢
  refine le_of_mul_le_mul_right ?_ hκ
  have h1 : ((K : ℝ) ^ 2 + 2 * k * m + G / K) * K = (K : ℝ) ^ 3 + K * (2 * k * m) + G := by field_simp
  rw [h1]
  linarith
end GeneralPieces.TopDisplay
