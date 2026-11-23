-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.card_latticeQuotient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:40.052897+00:00
-- url     : https://prove2.me/submissions/d1f91911-9572-46c8-a5b0-786773998a47

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_det_mul_eq_pow_of_mul_eq_smul
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_pZn_le_intLattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_index_pZn
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_index_intLatticeOfMatrix
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_card_latticeQuotient_eq_relIndex

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) [NeZero p]
    (hAB : A * B = p • 1) (hdetA : A.det ≠ 0) :
    Nat.card (latticeQuotient n p A) = B.det.natAbs := by
  -- Step 1: |latticeQuotient| = pZn.relIndex L(A)
  rw [card_latticeQuotient_eq_relIndex n A p]
  -- Step 2: Use tower formula to compute pZn.relIndex L(A)
  have hcontain : pZn n p ≤ intLatticeOfMatrix n A := pZn_le_intLattice n A B p hAB
  -- Tower formula: pZn.relIndex L(A) * L(A).index = pZn.index
  have htower := AddSubgroup.relIndex_mul_index hcontain
  -- Substitute known indices
  have hpZn_idx : (pZn n p).index = p ^ n := index_pZn n p
  have hLA_idx : (intLatticeOfMatrix n A).index = A.det.natAbs := index_intLatticeOfMatrix n A hdetA
  rw [hpZn_idx, hLA_idx] at htower
  -- From det(A) * det(B) = p^n, get |det(A)| * |det(B)| = p^n
  have hprod := det_mul_eq_pow_of_mul_eq_smul n A B p hAB
  have habs_prod : A.det.natAbs * B.det.natAbs = p ^ n := by
    have habs : (A.det * B.det).natAbs = ((p : ℤ) ^ Fintype.card (Fin n)).natAbs := by
      rw [hprod]
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, Fintype.card_fin] at habs
    exact habs
  -- From htower: relIndex * |det(A)| = p^n
  -- From habs_prod: |det(A)| * |det(B)| = p^n
  -- Therefore: relIndex = |det(B)|
  have hdetA_pos : A.det.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hdetA
  -- relIndex = p^n / |det(A)| = |det(B)|
  have h1 : (pZn n p).relIndex (intLatticeOfMatrix n A) * A.det.natAbs = p ^ n := htower
  have h2 : A.det.natAbs * B.det.natAbs = p ^ n := habs_prod
  -- From h1 and h2: relIndex * |det(A)| = |det(A)| * |det(B)|
  -- Since |det(A)| ≠ 0, we can cancel to get relIndex = |det(B)|
  have heq : (pZn n p).relIndex (intLatticeOfMatrix n A) * A.det.natAbs =
      A.det.natAbs * B.det.natAbs := by rw [h1, h2]
  rw [mul_comm] at heq
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hdetA_pos) heq
end GroupTheoreticShannonCapacity.Lattice
