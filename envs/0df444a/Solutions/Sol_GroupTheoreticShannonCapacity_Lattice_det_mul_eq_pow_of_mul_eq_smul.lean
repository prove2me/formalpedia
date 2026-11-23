-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.det_mul_eq_pow_of_mul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:11.313859+00:00
-- url     : https://prove2.me/submissions/a72a2b66-4712-422b-ad28-ac7d3e203bc0

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
theorem _root_.solution (n : ℕ) [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ) (hAB : A * B = p • 1) :
    A.det * B.det = (p : ℤ) ^ (Fintype.card (Fin n)) := by
  have h1 : (A * B).det = A.det * B.det := Matrix.det_mul A B
  have h2 : (p • (1 : Matrix (Fin n) (Fin n) ℤ)).det = (p : ℤ) ^ Fintype.card (Fin n) := by
    have : p • (1 : Matrix (Fin n) (Fin n) ℤ) = (p : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
      ext i j; simp [Matrix.smul_apply]
    rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
  rw [← h1, hAB, h2]
end GroupTheoreticShannonCapacity.Lattice
