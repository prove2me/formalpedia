-- Prove2me | solution 1 for MIPRE.Introspection.HonestMagicSquare.grid_isObservable
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:04:20.246897+00:00
-- url     : https://prove2.me/submissions/6ef03c3b-c9a8-4901-b779-13257ff1cfa2

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestMagicSquare.lean (solution of MIPRE.Introspection.HonestMagicSquare.grid_isObservable);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma X_mul_self : X * X = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X]
  · fin_cases j <;> simp [X]
end
end MIPRE.LCS.Pauli

namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma Z_mul_self : Z * Z = 1 := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Z]
  · fin_cases j <;> simp [Z]
end
end MIPRE.LCS.Pauli

namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma star_X : star X = X := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [X, Matrix.star_apply]
  · fin_cases j <;> simp [X, Matrix.star_apply]
end
end MIPRE.LCS.Pauli

namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma star_Z : star Z = Z := by
  ext i j
  fin_cases i
  · fin_cases j <;> simp [Z, Matrix.star_apply]
  · fin_cases j <;> simp [Z, Matrix.star_apply]
end
end MIPRE.LCS.Pauli

namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma isObservable_X : IsObservable X where
  involutive := X_mul_self
  self_adjoint := star_X
end
end MIPRE.LCS.Pauli

namespace MIPRE.LCS.Pauli
section
open Matrix
open scoped Kronecker
lemma isObservable_Z : IsObservable Z where
  involutive := Z_mul_self
  self_adjoint := star_Z
end
end MIPRE.LCS.Pauli

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.HonestMagicSquare
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem _root_.solution {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A))
    (j : Fin 9) : IsObservable (grid A B j) := by
  fin_cases j <;> simp only [grid]
  · exact observable_kronecker hA observable_one
  · exact observable_kronecker observable_one Pauli.isObservable_X
  · exact observable_kronecker hA Pauli.isObservable_X
  · exact observable_kronecker observable_one Pauli.isObservable_Z
  · exact observable_kronecker hB observable_one
  · exact observable_kronecker hB Pauli.isObservable_Z
  · exact observable_kronecker hA Pauli.isObservable_Z
  · exact observable_kronecker hB Pauli.isObservable_X
  · rw [mul_kronecker_mul]
    exact observable_mul (observable_kronecker hA Pauli.isObservable_Z)
      (observable_kronecker hB Pauli.isObservable_X) (tensor_anticommute hAB ZX_anticomm)
end MIPRE.Introspection.HonestMagicSquare
