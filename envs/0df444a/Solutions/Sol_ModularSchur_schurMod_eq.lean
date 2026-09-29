-- Prove2me | solution 1 for ModularSchur.schurMod_eq
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:18:58.834027+00:00
-- url     : https://prove2.me/submissions/7e6dcd23-ef55-4444-952d-152ac960b598

-- Generated from lean/ModularSchur/IntegerBridge.lean
--   imports : 2 platform node(s), 2 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : schurMod_eq -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Theorems.Thm_ModularSchur_schurModResidue_eq
import Theorems.Thm_ModularSchur_schurMod_eq_schurModResidue
import Mathlib

open Finset
variable {m : ℕ}

open ModularSchur in
theorem solution (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    schurMod m k ℓ = m / Nat.gcd m (ℓ - 1) - 1 := by
  rw [schurMod_eq_schurModResidue m k ℓ hm, schurModResidue_eq m k ℓ hm hℓ hk]
