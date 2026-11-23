-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.canonicalRep_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:38:38.667947+00:00
-- url     : https://prove2.me/submissions/aa1f260f-37cc-4fce-b173-78018fee1b7f

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
    (canonicalRep p z : ZMod p) = z := by
  unfold canonicalRep
  split_ifs with h
  · simp [ZMod.natCast_val]
  · simp [ZMod.natCast_val]
end GroupTheoreticShannonCapacity.Lattice
