-- Prove2me | solution 1 for Groundwork.Stepped.prodRange_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:31.453594+00:00
-- url     : https://prove2.me/submissions/a0706e33-ce87-4a1e-b31d-1ed5a8594478

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range
import Theorems.Thm_Groundwork_Stepped_foldRange_runs
import Theorems.Thm_Groundwork_Stepped_foldl_mul
import Theorems.Thm_Groundwork_Stepped_natAbs_prod_le
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
open Groundwork Groundwork.Stepped
open Finset
variable {α β γ : Type}
namespace Groundwork.Stepped
theorem _root_.solution [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} (t : ℕ → ℕ) (v : ℕ → ℤ)
    (V Sm : ℕ) (hV1 : 1 ≤ V) (hM : ∀ y < N a, M.Runs (a, y) (t y) Sm (v y))
    (hV : ∀ y < N a, (v y).natAbs ≤ V) :
    (prodRange N M).Runs a (∑ y ∈ range (N a), (t y + 1)) (size a + size (N a) + (size (V ^ N a) + Sm) + 1)
      (∏ y ∈ range (N a), v y) := by
  rw [← foldl_mul]
  refine foldRange_runs t v _ Sm hM fun k hk => ?_
  rw [show List.foldl (fun c y => mulG c y (v y)) (oneC a) (List.range k) = ∏ y ∈ range k, v y from foldl_mul v k]
  have h1 := natAbs_prod_le v V k fun y hy => hV y (by omega)
  have h2 := Nat.size_le_size (h1.trans (Nat.pow_le_pow_right hV1 hk))
  simp only [size_int, size_nat]; omega
end Groundwork.Stepped
