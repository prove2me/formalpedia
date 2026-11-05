-- Prove2me | solution 1 for GeneralPieces.TopDisplay.arg_le_km
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:36.565476+00:00
-- url     : https://prove2.me/submissions/a94b5563-a306-4bff-ab48-875d70722d74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_ClauseBound_Alg_TopArith_P_mul_le
import Theorems.Thm_ClauseBound_Alg_TopArith_sq_mul_lam_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
variable {K k m : ℕ}
namespace GeneralPieces.TopDisplay
theorem _root_.solution (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    K * (lamTopK K (3 * K ^ 8) k m + PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K)) ≤ 32 * (k * m) := by
  have h1 : K * lamTopK K (3 * K ^ 8) k m ≤ 8 * (k * m) :=
    (Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) K)).trans (sq_mul_lam_le hK hk hm)
  have h2 : K * (PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K)) ≤ 15 * (k * m) :=
    calc K * (PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K)) = PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K) * K := by ring
      _ ≤ PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K + 1) * K :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
      _ ≤ 15 * (k * m) := P_mul_le hK hk hm
  rw [Nat.mul_add]; omega
end GeneralPieces.TopDisplay
