-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.modPHom_image_intLattice_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:42.038435+00:00
-- url     : https://prove2.me/submissions/d7893d6a-34c3-4437-ad86-fe5fdcc05276

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
    (AddSubgroup.map (modPHom n p) (intLatticeOfMatrix n A) : Set (Fin n → ZMod p)) =
      latticeQuotient n p A := by
  ext x
  simp only [AddSubgroup.mem_map, SetLike.mem_coe]
  constructor
  · intro ⟨v, hv, hvx⟩
    obtain ⟨y, hvy⟩ := hv
    use y
    simp only [modPHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hvx
    ext i
    rw [← hvx, hvy]
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    rfl
  · intro ⟨y, hy⟩
    use A.mulVec y
    constructor
    · exact ⟨y, rfl⟩
    · simp only [modPHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      ext i
      rw [hy]
      simp only [Matrix.mulVec, dotProduct]
      push_cast
      rfl
end GroupTheoreticShannonCapacity.Lattice
