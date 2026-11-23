-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.distMod_eq_canonicalRep_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:08.635061+00:00
-- url     : https://prove2.me/submissions/afe26e39-0133-4162-b70c-0b405ff3eed2

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_distMod_eq_abs_canonicalRep

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (p : ℕ) [hp : NeZero p] (u v : ZMod p) :
    distMod p u v = Int.natAbs (canonicalRep p (u - v)) := by
  have h : distMod p u v = distMod p (u - v) 0 := by simp [distMod, sub_zero]
  rw [h, distMod_eq_abs_canonicalRep]
end GroupTheoreticShannonCapacity.Lattice
