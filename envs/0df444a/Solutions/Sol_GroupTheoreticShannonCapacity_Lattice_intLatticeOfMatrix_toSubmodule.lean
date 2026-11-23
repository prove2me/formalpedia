-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.intLatticeOfMatrix_toSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:39.359527+00:00
-- url     : https://prove2.me/submissions/009ca4ff-08f2-47fe-b6ba-33d7fb21bc5d

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
theorem _root_.solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    (intLatticeOfMatrix n A).toIntSubmodule = LinearMap.range A.mulVecLin := by
  apply SetLike.coe_injective
  rw [AddSubgroup.coe_toIntSubmodule, LinearMap.coe_range]
  ext v
  simp only [Set.mem_range, Matrix.mulVecLin_apply, intLatticeOfMatrix]
  constructor
  · intro ⟨x, hx⟩; exact ⟨x, hx.symm⟩
  · intro ⟨x, hx⟩; exact ⟨x, hx.symm⟩
end GroupTheoreticShannonCapacity.Lattice
