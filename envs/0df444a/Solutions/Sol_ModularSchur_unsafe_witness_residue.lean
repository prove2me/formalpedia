-- Prove2me | solution 1 for ModularSchur.unsafe_witness_residue
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T23:01:02.445352+00:00
-- url     : https://prove2.me/submissions/7b0c1457-1057-4a85-8ceb-c1ec617b8b0c

-- Generated from lean/ModularSchur/UnifiedValue.lean
--   imports : 0 platform node(s), 0 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : unsafe_witness_residue -> solution, hoisted out of the namespace
import Mathlib

open Finset Nat
variable {m ℓ : ℕ}

theorem solution (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    ((ℓ : ZMod m) - 1) * ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) = 0 := by
  norm_cast;
  simp +decide [ Int.subNatNat_of_le ( by linarith : 1 ≤ ℓ ) ];
  rw_mod_cast [ ← Nat.mul_div_assoc ];
  · rw [ Nat.mul_comm, Nat.mul_div_assoc ];
    · rw [ ZMod.natCast_eq_zero_iff ];
      exact dvd_mul_right _ _;
    · exact Nat.gcd_dvd_right _ _;
  · exact Nat.gcd_dvd_left _ _
