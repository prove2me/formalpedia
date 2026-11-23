-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.matrixA_entries_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:27.17251+00:00
-- url     : https://prove2.me/submissions/ae31b077-70fb-4db6-a05a-8ccd5a562d4d

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_p_q_are_integers


set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ A' : Matrix (Fin n) (Fin n) ℤ,
      matrixA n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = A'.map (↑· : ℤ → ℚ) := by
  -- Get that q is an integer
  obtain ⟨_, q', _, hq'⟩ := p_q_are_integers n k b r s hn hk hb
  -- Define the integer matrix
  let A'_entry : Fin n → Fin n → ℤ := fun i j =>
    if i = j then q'
    else if (i : ℕ) < (j : ℕ) then
      (r : ℤ) * (a n k b r s)^((j : ℕ) - (i : ℕ) - 1) * (s : ℤ)^(n - ((j : ℕ) - (i : ℕ) + 1))
    else  -- i > j
      -(k : ℤ) * (a n k b r s)^(n - ((i : ℕ) - (j : ℕ) + 1)) * (s : ℤ)^((i : ℕ) - (j : ℕ) - 1)
  use Matrix.of A'_entry
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, matrixA, matrixX, Matrix.add_apply,
             Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, X_entry, Matrix.of_apply, A'_entry]
  by_cases hij : i = j
  · -- Diagonal case: q • 1 + 0 = q'
    subst hij
    simp only [↓reduceIte, lt_self_iff_false, mul_one, add_zero, hq']
  · -- Off-diagonal case
    have hne_nat : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp only [hij, ↓reduceIte, mul_zero]
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · simp only [hlt, ↓reduceIte]
      push_cast
      ring
    · have hgt : (i : ℕ) > (j : ℕ) := Nat.lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_nat)
      simp only [hlt, hgt, ↓reduceIte]
      push_cast
      ring
end GroupTheoreticShannonCapacity.MainProofs
