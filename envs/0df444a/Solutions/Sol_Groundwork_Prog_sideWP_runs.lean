-- Prove2me | solution 1 for Groundwork.Prog.sideWP_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:17:29.964415+00:00
-- url     : https://prove2.me/submissions/44369da2-4214-42a8-ace6-86c4b2a2ae94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_CutProg
import Definitions.Def_StepMachines_Math_SideX
import Definitions.Def_StepMachines_Prog_Side
import Theorems.Thm_Groundwork_Grid_length_he
import Theorems.Thm_Groundwork_Grid_node_lt
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_map_range_eq_ofFn
import Theorems.Thm_Groundwork_Prog_size_two_pow
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_prodRange_runs
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
open Groundwork Groundwork.Prog
open Finset Stepped
open Groundwork.Grid (he node c2 rectDig sideChunk sideItem sideCap)
variable {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ)
variable {g tr lam}
namespace Groundwork.Prog
theorem _root_.solution [HasSize C] {R : Stepped (C × IQ) ℤ} {c : C} {B t S : ℕ} {Rm : Inst (Fin (g * g)) (List Bool)}
    (hR : ServesInst R c (lam c) B t S Rm) (y : ℕ) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : z.length = g ^ 3 * lam c) :
    (sideWP g tr lam R).Runs ((c, y), (a, z)) (g * (t + 1))
      (size ((c, y), (a, z)) + size g + (B * g + 2) + S + 3)
      (sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a, z))) a z) := by
  unfold sideWv
  cases hc : sideChk g tr lam ((c, y), (a, z)) with
  | false =>
    refine (ite_runs_false hc (const_runs (0 : ℤ) _)).mono ?_ ?_
    · have : 1 ≤ g * (t + 1) := Nat.mul_pos (by omega) (by omega)
      exact this
    · have : size (0 : ℤ) = 1 := rfl
      omega
  | true =>
    have hq : ∀ i < g, R.Runs (sideQuery g tr lam (((c, y), (a, z)), i)) t S
        (if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr (lam c) a z i u) else 1) ∧
        (if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr (lam c) a z i u)
          else 1).natAbs ≤ 2 ^ B := by
      intro i hi
      have hn := Grid.node_lt tr ha hi
      rw [dif_pos hn]
      have h := hR ⟨node g tr a i, hn⟩ (fun u => sideLabels g tr (lam c) a z i u) (fun u hu => by
        have : (u : ℕ) ≠ node g tr a i := fun h => hu (Fin.ext h)
        simp only [sideLabels, if_neg this]
        exact Grid.length_he hz hi u.2) (by simp [sideLabels])
      have e : sideQuery g tr lam (((c, y), (a, z)), i) =
          (c, node g tr a i, List.ofFn fun u : Fin (g * g) => sideLabels g tr (lam c) a z i u) := by
        simp only [sideQuery, map_range_eq_ofFn]
      rw [e]
      refine ⟨h.1, ?_⟩
      have := h.2
      rw [Int.abs_eq_natAbs] at this
      exact_mod_cast this
    have h := prodRange_runs (N := sideG g) (M := mapIn (sideQuery g tr lam) R) (a := ((c, y), (a, z))) (fun _ => t)
      (fun i => if h : node g tr a i < g * g then Rm ⟨node g tr a i, h⟩ (fun u => sideLabels g tr (lam c) a z i u)
        else 1)
      (2 ^ B) S Nat.one_le_two_pow (fun i hi => mapIn_runs (hq i hi).1) (fun i hi => (hq i hi).2)
    refine (ite_runs_true hc h).mono (by simp [sideG]) ?_
    have : size ((2 ^ B) ^ sideG g ((c, y), (a, z))) = B * g + 2 := by rw [sideG, ← pow_mul, size_two_pow]
    simp only [sideG] at this ⊢
    omega
end Groundwork.Prog
