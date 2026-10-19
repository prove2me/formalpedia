-- Prove2me | solution 1 for MIPRE.Introspection.HonestMagicSquare.cells_commute
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:04:20.897487+00:00
-- url     : https://prove2.me/submissions/05b6f7f9-df8b-4d71-8c48-d32ea6e421aa

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestMagicSquare.lean (solution of MIPRE.Introspection.HonestMagicSquare.cells_commute);
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
import Theorems.Thm_MIPRE_LCS_Pauli_X_anticomm_Z

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.HonestMagicSquare
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem _root_.solution {A B : Matrix I I ℂ}
    (hAB : A * B = -(B * A)) (c : Fin layout.r) (s t : Fin 3) :
    Commute (grid A B (cellIndex c s)) (grid A B (cellIndex c t)) := by
  have h := first_second_commute hAB c
  have h02 : Commute (grid A B (cellIndex c 0)) (grid A B (cellIndex c 2)) := by
    rw [third_eq]
    exact ((Commute.refl _).mul_right h).smul_right _
  have h12 : Commute (grid A B (cellIndex c 1)) (grid A B (cellIndex c 2)) := by
    rw [third_eq]
    exact (h.symm.mul_right (Commute.refl _)).smul_right _
  fin_cases s <;> fin_cases t
  · exact Commute.refl _
  · exact h
  · exact h02
  · exact h.symm
  · exact Commute.refl _
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact Commute.refl _
end MIPRE.Introspection.HonestMagicSquare
