-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.MainProofs.matrixB_entries_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:37.698819+00:00
-- url     : https://prove2.me/submissions/9ceff7de-1187-4876-a308-9cd338bad689

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MainProofs
open GroupTheoreticShannonCapacity Construction Lattice
namespace GroupTheoreticShannonCapacity.MainProofs
theorem _root_.solution (n k b r s : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) :
    ∃ B' : Matrix (Fin n) (Fin n) ℤ,
      matrixB n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) = B'.map (↑· : ℤ → ℚ) := by
  -- The diagonal coefficient (a - r) / b = k * b^(n-1) + s is an integer
  have hdiag : (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ) - (r : ℤ)) / (b : ℤ) =
               (k : ℤ) * (b : ℤ)^(n - 1) + (s : ℤ) := by
    have hb_ne : (b : ℤ) ≠ 0 := by omega
    simp only [a]
    have h : (k : ℤ) * (b : ℤ)^n + (s : ℤ) * (b : ℤ) + (r : ℤ) - (r : ℤ) =
             (b : ℤ) * ((k : ℤ) * (b : ℤ)^(n - 1) + (s : ℤ)) := by
      cases n with
      | zero => simp at hn
      | succ m => simp [pow_succ]; ring
    rw [h, Int.mul_ediv_cancel_left _ hb_ne]
  -- Define the integer matrix
  let diag_coef : ℤ := (k : ℤ) * (b : ℤ)^(n - 1) + (s : ℤ)
  let B'_entry : Fin n → Fin n → ℤ := fun i j =>
    if i = j then diag_coef
    else if (i : ℕ) < (j : ℕ) then
      -(r : ℤ) * (b : ℤ)^((j : ℕ) - (i : ℕ) - 1)
    else  -- i > j
      (k : ℤ) * (b : ℤ)^(n - ((i : ℕ) - (j : ℕ) + 1))
  use Matrix.of B'_entry
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, matrixB, matrixY, Matrix.add_apply,
             Matrix.smul_apply, Matrix.one_apply, Y_entry, Matrix.of_apply,
             B'_entry, diag_coef]
  by_cases hij : i = j
  · -- Diagonal case
    subst hij
    simp only [↓reduceIte, lt_self_iff_false, add_zero]
    rw [hdiag]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_pow, mul_one]
  · -- Off-diagonal case
    have hne_nat : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp only [hij, ↓reduceIte, smul_zero, zero_add]
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · simp only [hlt, ↓reduceIte]; norm_cast
    · have hgt : (i : ℕ) > (j : ℕ) := Nat.lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_nat)
      simp only [hlt, hgt, ↓reduceIte]; norm_cast
end GroupTheoreticShannonCapacity.MainProofs
