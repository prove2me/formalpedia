-- Prove2me | solution 1 for Groundwork.Prog.NetE.mergedM_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:03:19.524906+00:00
-- url     : https://prove2.me/submissions/91337cbe-7fb6-40cc-8b1a-345b3645e2bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Theorems.Thm_Groundwork_Prog_NetE_stLen_le
import Theorems.Thm_Groundwork_Prog_NetE_termM_runs
import Theorems.Thm_Groundwork_Prog_NetE_size_u_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_natAbs_prod_le
import Theorems.Thm_Groundwork_Stepped_prodRange_runs
import Theorems.Thm_Groundwork_Stepped_sumRange_runs
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
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable [HasSize C]
namespace Groundwork.Prog.NetE
theorem _root_.solution {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
    (hN : Np.Presents c N t S) (hS : N.Sized P B) (ht : 1 ≤ t) (x β m : ℕ)
    (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β)
    (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    (mergedM K g Np).Runs ((c, x), (G.val, List.ofFn θ))
      (2 ^ (P * m) * (g * g * (2 ^ P * (2 * t + 3) + 2) + 1))
      (S + 4 * (size c + size x + size K + K * (2 * β + 2)) + 5 * (P * m) + 2 * (B * (g * g)) + 3 * size (g * g)
        + 3 * P + 3 * B + 28)
      (mergedVal K g Np N ((c, x), (G.val, List.ofFn θ))) := by
  have hsu := size_u_le (c := c) (x := x) hθ hG
  have hst : stLen K g Np c x G ≤ P * m := stLen_le hN hS (hm G G.2)
  cases hv : validB K g Np ((c, x), (G.val, List.ofFn θ)) with
  | false =>
    have ev : mergedVal K g Np N ((c, x), (G.val, List.ofFn θ)) = 0 := by
      simp only [mergedVal, hv, if_false, Bool.false_eq_true]
    rw [ev]
    refine (ite_runs_false hv (const_runs (0 : ℤ) _)).mono
      (Nat.succ_le_of_lt (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _))) ?_
    have : size (0 : ℤ) = 1 := rfl
    omega
  | true =>
    have ev : mergedVal K g Np N ((c, x), (G.val, List.ofFn θ)) = ∑ y ∈ range (nStates K g Np ((c, x), (G.val, List.ofFn θ))),
        ∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) := by
      simp only [mergedVal, hv, if_true]
    rw [ev]
    have eN : nStates K g Np ((c, x), (G.val, List.ofFn θ)) = 2 ^ stLen K g Np c x G := rfl
    have hin : ∀ y < nStates K g Np ((c, x), (G.val, List.ofFn θ)), (prodRange (nPairs g) (termM K g Np)).Runs
        (((c, x), (G.val, List.ofFn θ)), y)
        (g * g * (2 ^ P * (2 * t + 2) + 1))
        (3 * (size ((c, x), (G.val, List.ofFn θ)) + (stLen K g Np c x G + 1)) + 3 * size (g * g) + B * (g * g)
            + 3 * P + 3 * B + S + 15)
        (∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) := by
      intro y hy
      have hy' : y.size ≤ stLen K g Np c x G := Nat.size_le.2 (eN ▸ hy)
      have := prodRange_runs (N := nPairs g) (M := termM K g Np) (a := (((c, x), (G.val, List.ofFn θ)), y))
        (fun _ => 2 ^ P * (2 * t + 2)) (fun i => termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) (2 ^ B)
        (2 * (size (((c, x), (G.val, List.ofFn θ)), y) + size (g * g)) + 3 * P + 3 * B + S + 12) Nat.one_le_two_pow
        (fun i hi => (termM_runs hN hS ht hβ hθ y hi).1.mono le_rfl (by
          have := Nat.size_le_size (Nat.le_of_lt hi)
          simp only [nPairs] at this
          simp only [size_prod, size_nat] at this ⊢
          omega))
        (fun i hi => (termM_runs hN hS ht hβ hθ y hi).2)
      refine this.mono (by simp [nPairs]) ?_
      simp only [nPairs, ← pow_mul]
      simp only [size_prod, size_nat, Nat.size_pow] at hsu ⊢
      omega
    have hout := sumRange_runs (N := nStates K g Np) (a := ((c, x), (G.val, List.ofFn θ)))
        (fun _ => g * g * (2 ^ P * (2 * t + 2) + 1))
      (fun y => ∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) ((2 ^ B) ^ (g * g)) _ hin
      (fun y _ => natAbs_prod_le _ _ _ fun i hi => (termM_runs hN hS ht hβ hθ y hi).2)
    refine (ite_runs_true hv hout).mono ?_ ?_
    · rw [sum_const, card_range, smul_eq_mul, eN]
      refine Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hst) (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 1)
      have : 2 ^ P * (2 * t + 2) ≤ 2 ^ P * (2 * t + 3) := Nat.mul_le_mul_left _ (by omega)
      omega
    · rw [eN, ← pow_mul, ← pow_add]
      simp only [size_nat, Nat.size_pow] at hsu ⊢
      omega
end Groundwork.Prog.NetE
