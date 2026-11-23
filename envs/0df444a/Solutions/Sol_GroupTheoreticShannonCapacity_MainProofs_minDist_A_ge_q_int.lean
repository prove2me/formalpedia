-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.minDist_A_ge_q_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:57:21.170923+00:00
-- url     : https://prove2.me/submissions/50994067-5ab0-455c-83a8-3535f2b2a523

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_minDist_A_ge_q


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n : ℕ) [NeZero n] (k b r s : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hrb : r ≤ b)
    (A' : Matrix (Fin n) (Fin n) ℤ) (q' : ℕ)
    (hA : matrixA n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = A'.map (↑· : ℤ → ℚ))
    (hq : (q' : ℚ) = Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) :
    minDistance n (latticeOfMatrix n (A'.map (↑· : ℤ → ℝ))) ≥ q' := by
  -- The key is showing the two matrices are equal when mapped to ℝ
  have hMinDist := Construction.minDist_A_ge_q n k b r s hk hb hrb
  -- Show A'.map (ℤ → ℝ) = matrixA.map (ℚ → ℝ)
  have hmatrix_eq : A'.map (↑· : ℤ → ℝ) =
      (matrixA n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)).map (↑· : ℚ → ℝ) := by
    rw [hA]
    ext i j
    simp only [Matrix.map_apply]
    -- (↑(A' i j : ℤ) : ℝ) = (↑(↑(A' i j : ℤ) : ℚ) : ℝ)
    norm_cast
  -- The lattices are equal
  rw [hmatrix_eq]
  -- Apply the bound and convert q to q'
  calc minDistance n (latticeOfMatrix n ((matrixA n k b r s).map (↑· : ℚ → ℝ)))
      ≥ (Construction.q n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) : ℝ) := hMinDist
    _ = (q' : ℝ) := by rw [← hq]; norm_cast
end GroupTheoreticShannonCapacity.MainProofs
