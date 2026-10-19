-- Prove2me | solution 1 for MIPRE.Introspection.HonestMagicSquare.constraint_wrong_parity
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:05:32.58608+00:00
-- url     : https://prove2.me/submissions/6d0ae128-441f-47ee-9143-7c9b7bdeef92

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestMagicSquare.lean (solution of MIPRE.Introspection.HonestMagicSquare.constraint_wrong_parity);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_cells_commute
import Theorems.Thm_MIPRE_Introspection_HonestMagicSquare_grid_isObservable
import Theorems.Thm_MIPRE_LCS_Pauli_X_anticomm_Z
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LCS
section
lemma sign_mul (a b : ZMod 2) :
    (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val = (-1 : ℂ) ^ (a + b).val := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp [ZMod.val_add]
end
end MIPRE.LCS

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
omit [StarModule ℂ R] in
lemma observable_mul_observableToProjector
    (O : R) (hO : IsObservable O) (a : ZMod 2) :
    O * observableToProjector O a =
      ((-1 : ℂ) ^ a.val) • observableToProjector O a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · simp [observableToProjector, observableSign, hO.involutive, mul_add,
      smul_add, add_comm]
  · simp [observableToProjector, observableSign, hO.involutive, mul_add,
      smul_add, add_comm]
end
end MIPRE.LCS

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- The first two observables in each actual row or column commute. -/
theorem first_second_commute {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) :
    Commute (grid A B (cellIndex c 0)) (grid A B (cellIndex c 1)) := by
  fin_cases c <;> simp only [cellIndex, cell, cellNat, grid]
  · exact tensor_commute (Commute.one_right _) (Commute.one_left _)
  · exact tensor_commute (Commute.one_left _) (Commute.one_right _)
  · exact tensor_anticommute hAB ZX_anticomm
  · exact tensor_commute (Commute.one_right _) (Commute.one_left _)
  · exact tensor_commute (Commute.one_left _) (Commute.one_right _)
  · exact tensor_anticommute hAB Pauli.X_anticomm_Z
end
end MIPRE.Introspection.HonestMagicSquare

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- The last cell is the signed product of the first two cells. -/
theorem third_eq (A B : Matrix I I ℂ) (c : Fin layout.r) :
    grid A B (cellIndex c 2) = ((-1 : ℂ) ^ (game.b c).val) •
      (grid A B (cellIndex c 0) * grid A B (cellIndex c 1)) := by
  fin_cases c <;> simp only [cellIndex, cell, cellNat, grid, game]
  all_goals norm_num
  all_goals rw [← mul_kronecker_mul]
  all_goals try simp only [mul_one, one_mul]
  rw [ZX_anticomm]
  ext i j
  exact mul_neg _ _
end
end MIPRE.Introspection.HonestMagicSquare

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- Every row has even parity and the last column has odd parity. -/
theorem row_product {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) :
    grid A B (cellIndex c 0) * grid A B (cellIndex c 1) * grid A B (cellIndex c 2) =
      ((-1 : ℂ) ^ (game.b c).val) • (1 : Matrix (I × Fin 2) (I × Fin 2) ℂ) := by
  rw [third_eq, mul_smul_comm]
  congr 1
  exact (observable_mul (grid_isObservable hA hB hAB _) (grid_isObservable hA hB hAB _)
    (first_second_commute hAB c)).involutive
end
end MIPRE.Introspection.HonestMagicSquare

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option backward.isDefEq.respectTransparency false in
theorem constraint_eigen {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (a : Fin 3 → ZMod 2) (j : Fin 3) :
    grid A B (cellIndex c j) * constraintOp A B c a =
      ((-1 : ℂ) ^ (a j).val) • constraintOp A B c a := by
  have he (j : Fin 3) : grid A B (cellIndex c j) * variableOp A B (cellIndex c j) (a j) =
      ((-1 : ℂ) ^ (a j).val) • variableOp A B (cellIndex c j) (a j) :=
    observable_mul_observableToProjector
      (grid A B (cellIndex c j)) (grid_isObservable hA hB hAB _) (a j)
  have hc (j k : Fin 3) : Commute (grid A B (cellIndex c j))
      (variableOp A B (cellIndex c k) (a k)) :=
    observable_commute_projector (cells_commute hAB c j k) (a k)
  change _ * (_ * _ * _) = _ • (_ * _ * _)
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · rw [← mul_assoc, ← mul_assoc, he 0, smul_mul_assoc, smul_mul_assoc]
  · calc
      _ = variableOp A B (cellIndex c 0) (a 0) *
          (grid A B (cellIndex c 1) * variableOp A B (cellIndex c 1) (a 1)) *
          variableOp A B (cellIndex c 2) (a 2) := by
        rw [← mul_assoc, ← mul_assoc, (hc 1 0).eq]
        simp only [mul_assoc]
      _ = _ := by rw [he 1, mul_smul_comm, smul_mul_assoc]
  · rw [← mul_assoc, (hc 2 0 |>.mul_right (hc 2 1)).eq, mul_assoc, he 2, mul_smul_comm]
end
end MIPRE.Introspection.HonestMagicSquare

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.HonestMagicSquare
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem _root_.solution {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (c : Fin layout.r) (a : Fin 3 → ZMod 2)
    (ha : a 0 + a 1 + a 2 ≠ game.b c) : constraintOp A B c a = 0 := by
  have h : ((-1 : ℂ) ^ (game.b c).val) • constraintOp A B c a =
      ((-1 : ℂ) ^ (a 0 + a 1 + a 2).val) • constraintOp A B c a := by
    calc
      _ = (grid A B (cellIndex c 0) * grid A B (cellIndex c 1) * grid A B (cellIndex c 2)) *
          constraintOp A B c a := by rw [row_product hA hB hAB, smul_mul_assoc, one_mul]
      _ = _ := by
        simp only [mul_assoc, constraint_eigen hA hB hAB, mul_smul_comm, smul_smul]
        congr 1
        rw [← sign_mul, ← sign_mul]
        ring
  have hs : ((-1 : ℂ) ^ (game.b c).val) - ((-1 : ℂ) ^ (a 0 + a 1 + a 2).val) ≠ 0 := by
    exact sub_ne_zero.mpr (fun hs => ha (sign_injective hs.symm))
  have hz : (((-1 : ℂ) ^ (game.b c).val) - ((-1 : ℂ) ^ (a 0 + a 1 + a 2).val)) •
      constraintOp A B c a = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hs
end MIPRE.Introspection.HonestMagicSquare
