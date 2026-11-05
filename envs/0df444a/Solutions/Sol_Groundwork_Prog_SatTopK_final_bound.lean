-- Prove2me | solution 1 for Groundwork.Prog.SatTopK.final_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:15.936203+00:00
-- url     : https://prove2.me/submissions/b7f91e16-5e70-45b7-b07c-39b24ed83d30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Math_SparsifyTree
import Definitions.Def_KSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_WidthK_Top_Sat

set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)
namespace Groundwork.Prog.SatTopK
theorem _root_.solution (P₁ P₂ Q A N : ℕ) (h1 : 1 ≤ N) :
    P₂ * N ^ 3 + A * (P₁ * N ^ 2) ^ A + 4 ≤ cOf P₁ P₂ Q A * N ^ cOf P₁ P₂ Q A ∧
      Q * N ^ 2 + 3 ≤ cOf P₁ P₂ Q A * N ^ cOf P₁ P₂ Q A := by
  have e3 : N ^ 3 ≤ N ^ cOf P₁ P₂ Q A := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have e2 : N ^ 2 ≤ N ^ cOf P₁ P₂ Q A := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have eA : N ^ (2 * A) ≤ N ^ cOf P₁ P₂ Q A := Nat.pow_le_pow_right h1 (by unfold cOf; omega)
  have e0 : 1 ≤ N ^ cOf P₁ P₂ Q A := Nat.one_le_pow _ _ h1
  generalize N ^ cOf P₁ P₂ Q A = P at e3 e2 eA e0
  have hc : cOf P₁ P₂ Q A * P = P₂ * P + A * P₁ ^ A * P + 2 * A * P + Q * P + 20 * P := by
    unfold cOf; ring
  have h3 : P₂ * N ^ 3 ≤ P₂ * P := Nat.mul_le_mul_left _ e3
  have h2 : Q * N ^ 2 ≤ Q * P := Nat.mul_le_mul_left _ e2
  have hA : A * (P₁ * N ^ 2) ^ A ≤ A * P₁ ^ A * P := by
    rw [mul_pow, ← pow_mul, ← mul_assoc]
    exact Nat.mul_le_mul_left _ eA
  rw [hc]
  constructor <;> omega
end Groundwork.Prog.SatTopK
