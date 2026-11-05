-- Prove2me | solution 1 for Groundwork.brute_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:47:05.912872+00:00
-- url     : https://prove2.me/submissions/e84a58e6-cf9c-488a-823d-c04383fa5799

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Definitions.Def_StepMachines_Prog_Brute
import Theorems.Thm_Groundwork_star_labelling_self
import Theorems.Thm_Groundwork_star_labelling_ne
import Theorems.Thm_Groundwork_query0_eq
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_natAbs_prod_le
import Theorems.Thm_Groundwork_Stepped_prodRange_runs
import Theorems.Thm_Groundwork_Stepped_sumRange_runs
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
import Theorems.Thm_Groundwork_sum_blocks_pairs
import Theorems.Thm_Groundwork_sum_toWord
import Theorems.Thm_Groundwork_tri_lt
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
open Finset Stepped
variable {C : Type} [HasSize C]
namespace Groundwork
theorem _root_.solution {K : ℕ} {lam : C → ℕ} {dflt : C → List Bool} {R : Stepped (C × ℕ × List (List Bool)) ℤ}
    {c : C} (Rm : Inst (Fin K) (List Bool)) (t S V : ℕ) (hV : 1 ≤ V)
    (hR : ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = lam c) → θ v = dflt c →
      R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ (Rm v θ).natAbs ≤ V) :
    (brute K lam dflt R).Runs c (2 ^ (K * (K - 1) / 2 * lam c) * (K * (t + 1) + 1))
      (size c + size (2 ^ (K * (K - 1) / 2 * lam c)) + (size (2 ^ (K * (K - 1) / 2 * lam c) * V ^ K) +
        (size c + size (2 ^ (K * (K - 1) / 2 * lam c)) + size K + (size (V ^ K) + S) + 1)) + 1)
      (Inst.ZW (lam c) (dflt c) Rm) := by
  set n := K * (K - 1) / 2 * lam c with hn
  -- the value at the node v under the labelling y
  let val : ℕ → ℕ → ℤ := fun y v =>
    if h : v < K then Rm ⟨v, h⟩ (star (labelling K (lam c) (dflt c) (toWord n y)) ⟨v, h⟩) else 1
  have hq : ∀ y (v : Fin K), R.Runs (c, query0 K (lam c) (dflt c) (toWord n y) v) t S (val y v) ∧
      (val y v).natAbs ≤ V := by
    intro y v
    rw [query0_eq]
    have e : val y v = Rm v (star (labelling K (lam c) (dflt c) (toWord n y)) v) := by
      simp only [val, v.2, dif_pos]
    rw [e]
    refine hR v _ (fun u hu => ?_) ?_
    · rw [star_labelling_ne _ _ _ _ hu]
      refine length_block ?_
      rw [length_toWord]
      have hne : v.1 ≠ u.1 := fun h => hu (Fin.ext h.symm)
      exact Nat.mul_le_mul_right _ (tri_lt (min_lt_max.2 hne) (max_lt v.2 u.2))
    · exact star_labelling_self _ _ _ _ v
  have hin : ∀ y < 2 ^ n, (prodRange (Function.const (C × ℕ) K) (mapIn (bruteQuery K lam dflt) R)).Runs
      (c, y) (K * (t + 1)) (size c + size (2 ^ n) + size K + (size (V ^ K) + S) + 1)
      (∏ v ∈ range K, val y v) := by
    intro y hy
    have := prodRange_runs (N := Function.const (C × ℕ) K) (a := (c, y))
      (M := mapIn (bruteQuery K lam dflt) R)
      (fun _ => t) (val y) V S hV
      (fun v hv => mapIn_runs (hq y ⟨v, hv⟩).1) (fun v hv => (hq y ⟨v, hv⟩).2)
    simp only [Function.const_apply] at this
    refine this.mono (by simp) ?_
    have := Nat.size_le_size hy.le
    simp only [size_prod, size_nat]; omega
  have hout := sumRange_runs (N := bruteBound K lam) (a := c)
    (fun _ => K * (t + 1)) (fun y => ∏ v ∈ range K, val y v) (V ^ K) _ hin
    (fun y _ => natAbs_prod_le (val y) V K fun v hv => (hq y ⟨v, hv⟩).2)
  have e1 : ∑ y ∈ range (2 ^ n), (K * (t + 1) + 1) = 2 ^ n * (K * (t + 1) + 1) := by simp
  have e2 : ∑ y ∈ range (2 ^ n), ∏ v ∈ range K, val y v = Inst.ZW (lam c) (dflt c) Rm := by
    unfold Inst.ZW
    rw [← sum_blocks_pairs K (lam c) (dflt c) fun Λ => ∏ v, Rm v (star Λ v), ← sum_toWord]
    refine sum_congr rfl fun y _ => ?_
    rw [prod_range]
    refine prod_congr rfl fun v _ => ?_
    simp only [val, v.2, dif_pos]
    rfl
  rw [← e1, ← e2]
  exact hout
end Groundwork
