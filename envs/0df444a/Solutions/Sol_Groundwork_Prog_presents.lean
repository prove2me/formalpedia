-- Prove2me | solution 1 for Groundwork.Prog.presents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:45.075194+00:00
-- url     : https://prove2.me/submissions/981532ab-ba30-4268-b8dc-a9e6fd82282d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatArith
import Definitions.Def_StepMachines_Prog_Count
import Theorems.Thm_Groundwork_Prog_size_word
import Theorems.Thm_Groundwork_Prog_size_fin
import Theorems.Thm_Groundwork_Prog_size_boole
import Theorems.Thm_Groundwork_Prog_capF_le
import Theorems.Thm_Groundwork_Prog_Count_lab_wordNet
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_ofFun_runs
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
open Groundwork Groundwork.Prog
open Finset Groundwork.Prog.Count
namespace Groundwork.Prog
theorem _root_.solution {g k : ℕ} (hg : 0 < g) (φ : Fml) : (satP g k).Presents φ (wordNet g k φ) 1 (S₀ g k φ) where
  S_eq _ := rfl
  c_eq _ _ _ := rfl
  lab_eq a b _ := lab_wordNet a b
  W_runs a z hz := by
    refine (Stepped.ofFun_runs (wF g k) (φ, (a.val, z))).mono le_rfl ?_
    have h1 := size_fin a
    have h2 : size (wF g k (φ, (a.val, z))) ≤ 2 := size_boole _
    have h3 : z.length = mu g φ * k := hz
    simp only [size_prod, size_word, S₀, h3] at *
    omega
  f_runs a b z θ hab hz hθ := by
    refine (Stepped.ofFun_runs (fF g k) (φ, ((a.val, b.val), (z, θ)))).mono le_rfl ?_
    have h1 := size_fin a
    have h1' := size_fin b
    have h2 : size (fF g k (φ, ((a.val, b.val), (z, θ)))) ≤ 2 := by
      unfold fF
      split_ifs <;> simp
    have h3 : z.length = mu g φ * k := hz
    have h4 : θ.length = capF g k φ a.val b.val := hθ
    have h5 := capF_le (k := k) hg φ hab
    simp only [size_prod, size_word, S₀, h3, h4] at *
    omega
end Groundwork.Prog
