-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.abs_canonicalRep_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:07.502095+00:00
-- url     : https://prove2.me/submissions/054efd45-b510-4164-9bd3-58df58da21ee

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
    |canonicalRep p z| ≤ p / 2 := by
  simp only [canonicalRep]
  split_ifs with h
  · rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact Int.ofNat_le.mpr h
  · push_neg at h
    have hzlt : z.val < p := z.val_lt
    have hneg : (z.val : ℤ) - p < 0 := by omega
    rw [abs_of_neg hneg]
    omega
end GroupTheoreticShannonCapacity.Lattice
