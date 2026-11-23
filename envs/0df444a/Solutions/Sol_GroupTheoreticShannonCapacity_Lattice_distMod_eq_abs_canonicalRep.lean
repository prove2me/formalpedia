-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.distMod_eq_abs_canonicalRep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:38:08.181795+00:00
-- url     : https://prove2.me/submissions/e302c6fb-bf23-4e1b-b39c-4913c3c6a277

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (p : ℕ) [hp : NeZero p] (z : ZMod p) :
    distMod p z 0 = Int.natAbs (canonicalRep p z) := by
  simp only [distMod, sub_zero, canonicalRep]
  split_ifs with h
  · -- z.val ≤ p / 2, so min z.val (p - z.val) = z.val
    rw [Int.natAbs_natCast]
    have : z.val ≤ p - z.val := by omega
    exact Nat.min_eq_left this
  · -- z.val > p / 2, so min z.val (p - z.val) = p - z.val
    push_neg at h
    have hlt : p - z.val < z.val := by omega
    rw [Nat.min_eq_right (le_of_lt hlt)]
    have hzlt : z.val < p := z.val_lt
    omega
end GroupTheoreticShannonCapacity.Lattice
