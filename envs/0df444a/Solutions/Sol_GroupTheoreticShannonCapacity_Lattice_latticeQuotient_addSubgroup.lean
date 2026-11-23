-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.latticeQuotient_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:51.693856+00:00
-- url     : https://prove2.me/submissions/c651d7f4-44d4-40c8-bfdf-94bf52f42bd1

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
theorem _root_.solution (n : ℕ) (p : ℕ) [NeZero p] (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ H : AddSubgroup (Fin n → ZMod p),
      (H : Set (Fin n → ZMod p)) = latticeQuotient n p A := by
  use {
    carrier := latticeQuotient n p A
    add_mem' := by
      intro a b ⟨x, hx⟩ ⟨y, hy⟩
      use x + y
      ext i
      simp only [hx, hy, Pi.add_apply, ← Finset.sum_add_distrib]
      congr 1
      ext j
      push_cast
      ring
    zero_mem' := by
      use 0
      ext i
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, Finset.sum_const_zero]
    neg_mem' := by
      intro a ⟨x, hx⟩
      use -x
      ext i
      simp only [hx, Pi.neg_apply, ← Finset.sum_neg_distrib]
      congr 1
      ext j
      push_cast
      ring
  }
  rfl
end GroupTheoreticShannonCapacity.Lattice
