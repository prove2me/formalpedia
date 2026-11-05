-- Prove2me | solution 1 for GeneralPieces.TopDisplay.terms_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:09.956461+00:00
-- url     : https://prove2.me/submissions/15318ad4-6269-409c-ad21-2a9a067be7bb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_GeneralPieces_TopDisplay_terms_le_gen

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA
namespace GeneralPieces.TopDisplay
theorem _root_.solution (K k m : ℕ) (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) (hm' : m ≤ K ^ 90) :
    (k : ℝ) * m / K ≤ k * (m : ℝ) ^ (1 - 1 / 90 : ℝ) ∧
    (K : ℝ) ^ 8 * Real.logb 2 K ≤ 20 * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) ∧
    (K : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m) ≤ 182 * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by
  have h := terms_le_gen K k m 10 hK hk (by norm_num) hm hm'
  have e1 : (1 - 1 / (9 * ((10 : ℕ) : ℝ))) = (1 - 1 / 90 : ℝ) := by norm_num
  have e2 : (2 * ((10 : ℕ) : ℝ)) = 20 := by norm_num
  have e3 : (2 + 18 * ((10 : ℕ) : ℝ)) = 182 := by norm_num
  rw [e1, e2, e3] at h
  exact h
end GeneralPieces.TopDisplay
