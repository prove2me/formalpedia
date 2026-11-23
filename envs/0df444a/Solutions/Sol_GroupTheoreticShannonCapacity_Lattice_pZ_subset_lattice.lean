-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.pZ_subset_lattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:49.035957+00:00
-- url     : https://prove2.me/submissions/b3d8f8ed-bf40-4bbe-99bb-968e0de32848

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
    (hAB : A * B = p • 1) :
    ∀ v : Fin n → ℤ, (fun i => (p * v i : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)) := by
  intro v
  -- p * v = (AB) * v = A * (B * v), so use B * v as the integer coordinates
  use fun j => ∑ k, B j k * v k
  ext i
  simp only [Matrix.mulVec, Matrix.map_apply, dotProduct]
  -- Goal: (p * v i : ℝ) = ∑ j, (A i j : ℝ) * (∑ k, (B j k * v k : ℝ))
  -- Step 1: Prove the equality in ℤ
  have hABv : ((A * B).mulVec v) i = (p : ℤ) * v i := by
    rw [hAB]
    -- Goal: ((p • 1) *ᵥ v) i = ↑p * v i
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, nsmul_eq_mul]
  have hAssoc : (A * B).mulVec v = A.mulVec (B.mulVec v) := (mulVec_mulVec v A B).symm
  have key : (p : ℤ) * v i = ∑ j, A i j * (∑ k, B j k * v k) := by
    rw [← hABv, hAssoc]
    simp only [Matrix.mulVec, dotProduct]
  -- Step 2: Cast to ℝ (only distribute cast over outer sum, not inner)
  have key_real := congrArg (Int.cast (R := ℝ)) key
  push_cast at key_real
  convert key_real using 2
  simp only [Int.cast_sum, Int.cast_mul]
end GroupTheoreticShannonCapacity.Lattice
