-- Prove2me | solution 1 for GeneralPieces.TopDisplay.K_ge_root90
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:41.634595+00:00
-- url     : https://prove2.me/submissions/cc5d60dd-7944-441e-84b6-a5eddf27b0af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_m_lt_pow
import Theorems.Thm_GeneralPieces_TopDisplay_root90_le

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (x₀ l m : ℕ) (hx : 1 ≤ x₀) (h : m < K x₀ (l + 1) ^ 9) : (m : ℝ) ^ (1 / 90 : ℝ) ≤ K x₀ l :=
  root90_le _ _ (m_lt_pow x₀ l m hx h).le
end GeneralPieces.TopDisplay
