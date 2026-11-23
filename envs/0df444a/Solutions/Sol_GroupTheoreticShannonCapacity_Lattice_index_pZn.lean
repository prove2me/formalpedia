-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.index_pZn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:43.794999+00:00
-- url     : https://prove2.me/submissions/c48e6f20-5c07-45b1-a70f-abf8464b10f6

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_modPHom_ker
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_modPHom_surjective

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (n : ℕ) [NeZero n] (p : ℕ) [NeZero p] :
    (pZn n p).index = p ^ n := by
  rw [AddSubgroup.index_eq_card]
  have hker : (modPHom n p).ker = pZn n p := modPHom_ker n p
  have hsurj := modPHom_surjective n p
  -- By first isomorphism theorem: (Fin n → ℤ) / ker ≅ (Fin n → ZMod p)
  have hequiv := QuotientAddGroup.quotientKerEquivOfSurjective (modPHom n p) hsurj
  rw [← hker]
  rw [Nat.card_congr hequiv.toEquiv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
end GroupTheoreticShannonCapacity.Lattice
