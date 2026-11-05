-- Prove2me | solution 1 for GeneralPieces.Top.Lof_le_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:09:33.447378+00:00
-- url     : https://prove2.me/submissions/f00d9a61-7d59-4628-b3fc-ec75b577f6d6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Top_CaseI

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Top
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg CountKSat
namespace GeneralPieces.Top
theorem _root_.solution {K g P Uv Ub : ℕ} (hK : 0 < K) (hU : Uv ≤ Ub) : AppRunningTime.Lof K g (1 / (2 * (K : ℝ))) P Uv ≤ (K ^ 3 + K * Ub + g * P) / K ^ 3 := by
  have hK3 : 0 < K ^ 3 := Nat.pow_pos hK
  have h1 := Nat.lt_mul_div_succ (K ^ 3 + K * Ub + g * P) hK3
  generalize (K ^ 3 + K * Ub + g * P) / K ^ 3 = β at *
  have h2 : K * Uv + g * P ≤ K ^ 3 * β := by
    have := Nat.mul_le_mul_left K hU
    have e : K ^ 3 * (β + 1) = K ^ 3 * β + K ^ 3 := by ring
    omega
  have h3 : (K : ℝ) * Uv + g * P ≤ (K : ℝ) ^ 3 * β := by exact_mod_cast h2
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold AppRunningTime.Lof
  rw [Nat.ceil_le, div_le_iff₀ (by positivity)]
  have e : (Uv : ℝ) + 2 * (1 / (2 * (K : ℝ))) * g * P = (K * Uv + g * P) / K := by field_simp
  rw [e, div_le_iff₀ hKr]
  calc (K : ℝ) * Uv + g * P ≤ (K : ℝ) ^ 3 * β := h3
    _ = β * (K : ℝ) ^ 2 * K := by ring
end GeneralPieces.Top
