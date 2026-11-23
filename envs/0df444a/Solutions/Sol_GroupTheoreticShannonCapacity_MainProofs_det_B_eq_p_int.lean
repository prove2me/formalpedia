-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.det_B_eq_p_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:53:03.338055+00:00
-- url     : https://prove2.me/submissions/a19b3377-1435-413a-a76e-ce5416a48be6

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_det_B_eq_p


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n : ℕ) (k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (B' : Matrix (Fin n) (Fin n) ℤ) (p' : ℕ)
    (hB : matrixB n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = B'.map (↑· : ℤ → ℚ))
    (hp : (p' : ℚ) = Construction.p n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) :
    B'.det = p' := by
  -- Use det_B_eq_p and that det commutes with ring homomorphisms
  have hDetB_rat := Construction.det_B_eq_p n k b r s hn (by omega : 1 ≤ (k : ℤ))
      (by omega : 1 ≤ (b : ℤ)) (by omega : 0 ≤ (r : ℤ)) (by omega : 0 ≤ (s : ℤ))
  -- matrixB.det = p over ℚ; rewrite using hB and ← hp
  rw [hB, ← hp] at hDetB_rat
  -- det commutes with ring homs: (B'.map).det = (B'.det : ℚ)
  have hdet_map : (B'.map (↑· : ℤ → ℚ)).det = (B'.det : ℚ) := by
    rw [← Int.cast_det]
  rw [hdet_map] at hDetB_rat
  -- B'.det = p' by injectivity of ℤ → ℚ
  have h : (B'.det : ℚ) = (p' : ℚ) := hDetB_rat
  exact_mod_cast h
end GroupTheoreticShannonCapacity.MainProofs
