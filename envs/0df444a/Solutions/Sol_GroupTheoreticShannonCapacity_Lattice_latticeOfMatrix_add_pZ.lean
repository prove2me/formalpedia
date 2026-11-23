-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Lattice.latticeOfMatrix_add_pZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:32.0288+00:00
-- url     : https://prove2.me/submissions/6c9ff2e5-995d-41d1-a07e-1b2902cf9b78

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Theorems.Thm_GroupTheoreticShannonCapacity_Lattice_pZ_subset_lattice

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Lattice
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity.Lattice
theorem _root_.solution (n : ℕ) [NeZero n] (A B : Matrix (Fin n) (Fin n) ℤ) (p : ℕ)
    (hAB : A * B = p • 1)
    (v : Fin n → ℤ) (hv : (fun i => (v i : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)))
    (k : Fin n → ℤ) :
    (fun i => ((v i + p * k i) : ℝ)) ∈ latticeOfMatrix n (A.map (↑· : ℤ → ℝ)) := by
  obtain ⟨x, hx⟩ := hv
  have hpk := pZ_subset_lattice n A B p hAB k
  obtain ⟨y, hy⟩ := hpk
  use x + y
  ext i
  have hvi : (v i : ℝ) = (A.map (↑· : ℤ → ℝ)).mulVec (fun j => (x j : ℝ)) i := congrFun hx i
  have hpki : ((p : ℕ) * k i : ℝ) = (A.map (↑· : ℤ → ℝ)).mulVec (fun j => (y j : ℝ)) i :=
    congrFun hy i
  simp only [Pi.add_apply, hvi, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [show ((p : ℕ) : ℝ) * (k i : ℝ) = ((p : ℕ) * k i : ℝ) by ring, hpki]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← Finset.sum_add_distrib]
  congr 1
  ext j
  push_cast
  ring
end GroupTheoreticShannonCapacity.Lattice
