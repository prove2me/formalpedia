-- Prove2me | solution 1 for ModularSchur.schurModResidue_eq
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:15:04.415502+00:00
-- url     : https://prove2.me/submissions/ad6bc23d-27b8-4b8e-af07-3400970ffb3f

-- Generated from lean/ModularSchur/Partition.lean
--   imports : 2 platform node(s), 1 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : schurModResidue_eq -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_le_schurModResidue
import Theorems.Thm_ModularSchur_schurModResidue_le
import Mathlib

open Finset
variable {m : ℕ}

open ModularSchur in
theorem solution (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    schurModResidue m k ℓ = m / Nat.gcd m (ℓ - 1) - 1 :=
  le_antisymm (schurModResidue_le m k ℓ hm hℓ) (le_schurModResidue m k ℓ hm hℓ hk)
