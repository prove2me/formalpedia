-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.AB_eq_pI_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:57:08.281106+00:00
-- url     : https://prove2.me/submissions/5665bb11-4854-4fbf-a8f5-114c45fc7648

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_AB_eq_pI


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (A' : Matrix (Fin n) (Fin n) ℤ) (B' : Matrix (Fin n) (Fin n) ℤ) (p' : ℕ)
    (hA : matrixA n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = A'.map (↑· : ℤ → ℚ))
    (hB : matrixB n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = B'.map (↑· : ℤ → ℚ))
    (hp : (p' : ℚ) = Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) :
    A' * B' = p' • 1 := by
  -- Use AB_eq_pI and injectivity of ℤ → ℚ
  have hAB_rat := Construction.AB_eq_pI n k b r s hn hk hb
  -- Rewrite using hA, hB, and ← hp to get equation over ℚ
  rw [hA, hB, ← hp] at hAB_rat
  -- Now prove entrywise using injectivity
  ext i j
  have hinj : Function.Injective (↑· : ℤ → ℚ) := Int.cast_injective
  apply hinj
  change ((A' * B') i j : ℚ) = ((p' • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℚ)
  -- LHS: ((A' * B') i j : ℚ) = ((A'.map) * (B'.map)) i j
  have hlhs : ((A' * B') i j : ℚ) = ((A'.map (↑· : ℤ → ℚ)) * (B'.map (↑· : ℤ → ℚ))) i j := by
    simp only [Matrix.mul_apply, Matrix.map_apply]
    push_cast; rfl
  -- RHS: ((p' • 1) i j : ℚ) = (p' • 1 : Matrix _ _ ℚ) i j
  have hrhs : ((p' • (1 : Matrix (Fin n) (Fin n) ℤ)) i j : ℚ) =
              ((p' : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ)) i j := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j <;> simp [hij]
  rw [hlhs, hrhs]
  -- From hAB_rat: (A'.map) * (B'.map) = p' • 1
  exact congrFun (congrFun hAB_rat i) j
end GroupTheoreticShannonCapacity.MainProofs
