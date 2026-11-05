-- Prove2me | solution 1 for Groundwork.TM.run_inside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:37.331994+00:00
-- url     : https://prove2.me/submissions/adfedfc4-8d68-4e30-84d2-31400a3a4496

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main


attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd4_cnt
section
namespace Groundwork.TM
open Turing
section
variable (A B₁ B₂ C W : List Sym)
end
section steps
variable (p₁ p₂ : Bool) (A B₁ B₂ C : List Sym)
private theorem step_open : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.L :: A) B₁ B₂ C⟩ =
    some ⟨some .loop, none, st4 A (putIf p₁ [.R] B₁) (putIf p₂ [.R] B₂) (.R :: C)⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, pushIf, putIf, TM2.stepAux]
private theorem step_bit_in (b : Bool) : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.bit b :: A) B₁ B₂ (.R :: C)⟩ =
    some ⟨some .loop, none, st4 A (putIf p₁ [.bit b] B₁) (putIf p₂ [.bit b] B₂) (.R :: C)⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, mvChk, pushIf, putIf, TM2.stepAux]
private theorem step_close_in : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.R :: A) B₁ B₂ (.R :: .R :: C)⟩ =
    some ⟨some .loop, none, st4 A (putIf p₁ [.L] B₁) (putIf p₂ [.L] B₂) (.R :: C)⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, mvChk, pushIf, putIf, TM2.stepAux]
end steps
private theorem putIf_nil (p : Bool) (B : List Sym) : putIf p (mirror (code .nil)) B = putIf p [.L] (putIf p [.R] B) := by
  cases p <;> simp [putIf, code, mirror, Sym.flip]
private theorem putIf_cons (p : Bool) (x y : V) (B : List Sym) : putIf p (mirror (code (.cons x y))) B =
    putIf p [.L] (putIf p (mirror (code y)) (putIf p (mirror (code x)) (putIf p [.R] B))) := by
  cases p <;> simp [putIf, code, mirror, Sym.flip]
private theorem code_cons_append (x y : V) (A : List Sym) : code (.cons x y) ++ A = .L :: (code x ++ (code y ++ (.R :: A))) := by
  simp [code]
private theorem length_code_cons (x y : V) : (code (.cons x y)).length = 1 + (code x).length + (code y).length + 1 := by
  simp [code]; omega
end Groundwork.TM
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
namespace Groundwork.TM
theorem _root_.solution (p₁ p₂ : Bool) : ∀ (x : V) (A B₁ B₂ C : List Sym),
    Run (TM2.step (mvM p₁ p₂)) ⟨some .loop, none, st4 (code x ++ A) B₁ B₂ (.R :: C)⟩ (code x).length
      ⟨some .loop, none, st4 A (putIf p₁ (mirror (code x)) B₁) (putIf p₂ (mirror (code x)) B₂) (.R :: C)⟩
  | .bit b, A, B₁, B₂, C => Run.one (step_bit_in p₁ p₂ A B₁ B₂ C b)
  | .nil, A, B₁, B₂, C => by
    rw [putIf_nil, putIf_nil]
    exact (Run.one (step_open p₁ p₂ (.R :: A) B₁ B₂ (.R :: C))).trans (Run.one (step_close_in p₁ p₂ A _ _ C))
  | .cons x y, A, B₁, B₂, C => by
    have h1 := Run.one (step_open p₁ p₂ (code x ++ (code y ++ (.R :: A))) B₁ B₂ (.R :: C))
    have h2 := solution p₁ p₂ x (code y ++ (.R :: A)) (putIf p₁ [.R] B₁) (putIf p₂ [.R] B₂) (.R :: C)
    have h3 := solution p₁ p₂ y (.R :: A) (putIf p₁ (mirror (code x)) (putIf p₁ [.R] B₁))
      (putIf p₂ (mirror (code x)) (putIf p₂ [.R] B₂)) (.R :: C)
    have h4 := Run.one (step_close_in p₁ p₂ A (putIf p₁ (mirror (code y)) (putIf p₁ (mirror (code x)) (putIf p₁ [.R] B₁)))
      (putIf p₂ (mirror (code y)) (putIf p₂ (mirror (code x)) (putIf p₂ [.R] B₂))) C)
    rw [code_cons_append, putIf_cons, putIf_cons, length_code_cons]
    exact ((h1.trans h2).trans h3).trans h4
end Groundwork.TM
