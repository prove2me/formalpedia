-- Prove2me | solution 1 for ModularSchur.schurModResidue_k1_all
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:16:51.910784+00:00
-- url     : https://prove2.me/submissions/394a6a70-6944-4e05-922c-d8d668e3f0e4

-- Generated from lean/ModularSchur/K1Theorem.lean
--   imports : 2 platform node(s), 1 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : schurModResidue_k1_all -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_schurModResidue_k1
import Theorems.Thm_ModularSchur_schurModResidue_k1_of_modulus_lt
import Mathlib

open Finset Classical
variable {m ℓ : ℕ}

open ModularSchur in
theorem solution (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    schurModResidue m 1 ℓ =
      if ℓ ≤ m then min (ℓ - 1) (m / ℓ) else if ℓ % m = 1 then 0 else 1 := by
  by_cases hlm : ℓ ≤ m
  · rw [if_pos hlm]
    exact schurModResidue_k1 m ℓ hm hℓ hlm
  · rw [if_neg hlm]
    exact schurModResidue_k1_of_modulus_lt m ℓ hm (by omega)
