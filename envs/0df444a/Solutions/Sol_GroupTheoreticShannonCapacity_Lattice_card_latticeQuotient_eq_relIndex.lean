-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.card_latticeQuotient_eq_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:42:01.05027+00:00
-- url     : https://prove2.me/submissions/6b74fb4d-b0b9-4596-8d95-768370ebd349

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_modPHom_ker
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_modPHom_image_intLattice_carrier

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (n : ℕ) [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) [NeZero p] :
    Nat.card (latticeQuotient n p A) = (pZn n p).relIndex (intLatticeOfMatrix n A) := by
  -- Use AddSubgroup.relIndex_ker: f.ker.relIndex K = Nat.card (K.map f)
  -- With f = modPHom and K = intLatticeOfMatrix
  have hker : (modPHom n p).ker = pZn n p := modPHom_ker n p
  have himage := modPHom_image_intLattice_carrier n p A
  -- relIndex_ker gives: (modPHom n p).ker.relIndex L(A) = Nat.card (L(A).map (modPHom))
  rw [← hker]
  rw [AddSubgroup.relIndex_ker (intLatticeOfMatrix n A) (modPHom n p)]
  -- Now show Nat.card (L(A).map modPHom) = Nat.card (latticeQuotient)
  -- The carriers are equal as sets
  have hset_eq : (latticeQuotient n p A) =
      (AddSubgroup.map (modPHom n p) (intLatticeOfMatrix n A) : Set (Fin n → ZMod p)) := himage.symm
  -- Construct an equiv between the two types
  have hequiv : (latticeQuotient n p A) ≃
      ↥(AddSubgroup.map (modPHom n p) (intLatticeOfMatrix n A)) := Equiv.setCongr hset_eq
  exact Nat.card_congr hequiv
end GroupTheoreticShannonCapacity.Lattice
