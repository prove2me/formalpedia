-- Prove2me | solution 1 for Groundwork.Grid.sideR_nodeC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:13:09.63681+00:00
-- url     : https://prove2.me/submissions/63802a5a-abf2-4710-bd7f-4c20743c1c11

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
import Theorems.Thm_Groundwork_Code_enc_dec
import Theorems.Thm_Groundwork_Grid_bitsC_full
import Theorems.Thm_Groundwork_Grid_bitsOf_eq_zero
import Theorems.Thm_Groundwork_length_block
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (w : Fin g × Fin g) {wn : List Bool}
    (h : wn.length = g * g * n) :
    sideR g tr n Rm w ((nodeC g tr n).dec wn) =
      if (block n ((gridE g tr).symm w) wn).all (!·) = true then
        Rm ((gridE g tr).symm w) (fun u => if u = (gridE g tr).symm w then [] else block n u wn)
      else 0 := by
  have hl : ∀ u : Fin (g * g), (block n u wn).length = n := fun u =>
    length_block (by rw [h]; exact Nat.mul_le_mul_right _ u.2)
  have hd : ∀ w', (nodeC g tr n).dec wn w' = bitsOf n (block n ((gridE g tr).symm w') wn) := fun _ => rfl
  unfold sideR onGrid instW
  simp only [hd, bitsOf_eq_zero (hl _), Equiv.symm_apply_apply]
  refine if_congr Iff.rfl (congrArg _ (funext fun u => if_congr Iff.rfl rfl ?_)) rfl
  exact (bitsC n).enc_dec (by rw [bitsC_full]; exact mem_words.2 (hl u))
end Groundwork.Grid
