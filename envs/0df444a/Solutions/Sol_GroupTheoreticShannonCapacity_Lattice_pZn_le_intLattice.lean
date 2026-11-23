-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.pZn_le_intLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:19.441961+00:00
-- url     : https://prove2.me/submissions/0630b149-d716-4b01-9322-9f9f30a82db3

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
theorem _root_.solution (n : ℕ) [NeZero n] (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ)
    (hAB : A * B = p • 1) : pZn n p ≤ intLatticeOfMatrix n A := by
  intro v ⟨x, hv⟩
  -- p * x = A * (B * x), so use B * x as the coordinate vector
  use B.mulVec x
  ext i
  -- First show A * (B * x) = (AB) * x = p * x
  have h1 : A.mulVec (B.mulVec x) = (A * B).mulVec x := by
    simp only [Matrix.mulVec_mulVec]
  have h2 : (A * B).mulVec x = (p • (1 : Matrix (Fin n) (Fin n) ℤ)).mulVec x := by
    rw [hAB]
  have h3 : ((p : ℕ) • (1 : Matrix (Fin n) (Fin n) ℤ)).mulVec x = (p : ℤ) • x := by
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [hv]
  -- Now connect (fun i => p * x i) i with A.mulVec (B.mulVec x) i
  have h4 : ((p : ℤ) • x) i = (p : ℤ) * x i := by simp [Pi.smul_apply]
  rw [h1, h2, h3, h4]
end GroupTheoreticShannonCapacity.Lattice
