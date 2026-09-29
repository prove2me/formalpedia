-- Prove2me | solution 1 for ModularSchur.no_valid_partition_of_ge_m
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T22:43:41.666131+00:00
-- url     : https://prove2.me/submissions/2a3990d0-f0b1-4253-bc47-6e707f208ecd

-- Generated from lean/ModularSchur/IntegerBridge.lean
--   imports : 0 platform node(s), 1 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : no_valid_partition_of_ge_m -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurIntegerBridge
import Mathlib

open Finset
variable {m : ℕ}

open ModularSchur in
theorem solution (hm : 2 ≤ m) {ℓ k N : ℕ}
    (hN : m ≤ N) (P : Fin k → Finset ℕ) (hP : IsValidPartitionNat m ℓ k N P) : False := by
  have hm_mem : m ∈ Finset.Ioc 0 N := by
    simp only [Finset.mem_Ioc]; omega
  obtain ⟨i, hi⟩ := hP.covers m hm_mem
  refine hP.sumFree i (fun _ => m) (fun _ => hi) m hi ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_mod_left, Nat.mod_self]
