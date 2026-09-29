-- Prove2me | solution 1 for ModularSchur.singleton_sumFree_iff
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-19T22:57:27.43354+00:00
-- url     : https://prove2.me/submissions/c0e07f29-06c2-4048-a635-a5094778dac0

-- Generated from lean/ModularSchur/SingletonSafety.lean
--   imports : 0 platform node(s), 1 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : singleton_sumFree_iff -> solution, hoisted out of the namespace
import Definitions.Def_ModularSchurBasic
import Mathlib

open Finset
variable {m : ℕ}

open ModularSchur in
theorem solution (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : ZMod m) :
    IsEllSumFree m ℓ {r} ↔ ((ℓ : ZMod m) - 1) * r ≠ 0 := by
  constructor <;> intro h <;> simp_all +decide [ IsEllSumFree ];
  · exact fun hr => h ( fun _ => r ) ( fun _ => rfl ) ( by linear_combination hr );
  · grind
