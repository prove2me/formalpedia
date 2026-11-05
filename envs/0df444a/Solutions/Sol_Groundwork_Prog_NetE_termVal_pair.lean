-- Prove2me | solution 1 for Groundwork.Prog.NetE.termVal_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:02:31.572934+00:00
-- url     : https://prove2.me/submissions/a706f03f-869d-4e69-99b3-14fd0a009b08

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_Prog_NetE_div_mod_pair
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
import Theorems.Thm_Groundwork_sum_toWord
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
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)
namespace Groundwork.Prog.NetE
theorem _root_.solution {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x : ℕ) (q : IQ) (y : ℕ) (a b : Fin g) :
    termVal K g Np N ((((c, x), q), y), a.val * g + b.val) =
      if col K x a ≠ q.1 ∨ (col K x b = q.1 ∧ b < a) then 1
      else if a = b then N.W a (zA K g Np (((c, x), q), y) a)
      else if col K x b = q.1 then N.Ψ a b (zA K g Np (((c, x), q), y) a) (zA K g Np (((c, x), q), y) b)
      else N.f a b (zA K g Np (((c, x), q), y) a) (labOf K g Np ((c, x), q) a b) := by
  obtain ⟨h1, h2⟩ := div_mod_pair a b
  unfold termVal isOne isW isPsi nLab
  simp only [h1, h2, valW, valF, a.2, b.2, and_self, dite_true, Fin.eta, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Fin.val_fin_lt, Fin.val_inj]
  split_ifs with h3 h4 h5
  · rfl
  · rfl
  · rw [sum_toWord (Np.cap c a b) (fun θ => N.f a b (zA K g Np (((c, x), q), y) a) θ *
      N.f b a (zA K g Np (((c, x), q), y) b) θ), Network.Ψ, hN.lab_eq a b h4]
  · rfl
end Groundwork.Prog.NetE
