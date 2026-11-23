-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.modPHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:36.591132+00:00
-- url     : https://prove2.me/submissions/e42b3420-f570-40e8-aafb-ba8436d4903a

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
theorem _root_.solution (n : ℕ) (p : ℕ) [NeZero p] :
    Function.Surjective (modPHom n p) := by
  intro x
  refine ⟨fun i => ((x i).val : ℤ), ?_⟩
  ext i
  simp only [modPHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  -- Goal: (((x i).val : ℤ) : ZMod p) = x i
  rw [Int.cast_natCast]
  -- Goal: ((x i).val : ZMod p) = x i
  exact ZMod.natCast_zmod_val (x i)
end GroupTheoreticShannonCapacity.Lattice
