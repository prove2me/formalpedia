-- Prove2me | solution 1 for Groundwork.SatNet.sized_net
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:23:08.767736+00:00
-- url     : https://prove2.me/submissions/b69b96eb-afbf-4a7f-a4dc-6abacbf033fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
import Theorems.Thm_P2M_Groundwork_SatNet___of_lt_d32e7cdb1e61
import Theorems.Thm_Groundwork_SatNet_sum_c_le
import Theorems.Thm_Groundwork_SatNet_abs_ite_le

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
variable [DecidableEq V]
variable {φ : List (List (V × Bool))} {g μ k : ℕ}
namespace Groundwork.SatNet
theorem _root_.solution (B : ℕ) : (net φ g μ k).Sized (2 * k * μ) B where
  card_S a := by
    simp only [net, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_assoc, Nat.mul_comm k]; omega)
  abs_W a z := by
    simp only [net, weight]
    exact (abs_ite_le _).trans (one_le_pow₀ (by norm_num))
  c_symm a b := by simp only [net, min_comm, max_comm]
  sum_c a := by
    refine (sum_c_le a).trans ?_
    have : #{s : Sl μ k | lit φ (a, s) ≠ none} ≤ μ * k := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    rw [Nat.mul_assoc, Nat.mul_comm k]
    omega
  card_lab a b hab := by
    have hlt : min a b < max a b := by
      rcases lt_or_gt_of_ne hab with h | h
      · rwa [min_eq_left h.le, max_eq_right h.le]
      · rwa [min_eq_right h.le, max_eq_left h.le]
    simp only [Network.lab, net, if_pos hlt, tuples, Fintype.card_piFinset]
    apply le_of_eq
    rw [Finset.prod_congr rfl (g := fun s => if Out φ (min a b) (max a b) s then 2 else 1)
      (fun s _ => by split_ifs <;> simp)]
    rw [Finset.prod_ite]
    simp
  abs_f a b z θ := by
    have h1 : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    simp only [net]
    split_ifs <;> simp [h1]
  abs_Ψ a b z z' hab := by
    rcases lt_or_gt_of_ne hab with h | h
    · rw [Ψ_of_lt h]; exact (abs_ite_le _).trans (one_le_pow₀ (by norm_num))
    · have : (net φ g μ k).Ψ a b z z' = (net φ g μ k).Ψ b a z' z := by
        simp only [Network.Ψ, Network.lab, min_comm, max_comm, mul_comm]
      rw [this, Ψ_of_lt h]; exact (abs_ite_le _).trans (one_le_pow₀ (by norm_num))
end Groundwork.SatNet
