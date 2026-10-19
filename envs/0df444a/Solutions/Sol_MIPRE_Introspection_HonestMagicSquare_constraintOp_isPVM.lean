-- Prove2me | solution 1 for MIPRE.Introspection.HonestMagicSquare.constraintOp_isPVM
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:05:29.860982+00:00
-- url     : https://prove2.me/submissions/deeee83a-3668-4996-81ee-3fe71fdc60d2

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/HonestMagicSquare.lean (solution of MIPRE.Introspection.HonestMagicSquare.constraintOp_isPVM);
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
import Theorems.Thm_MIPRE_LCS_isMeasurementSystem_observableToProjector

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
omit [StarRing R] [StarModule ℂ R] in
/-- If observables $O₁$ and $O₂$ commute, then all corresponding projectors
$P_a(O₁)$ and $P_b(O₂)$ commute as well. -/
lemma commute_observableToProjector {O1 O2 : R} (h : Commute O1 O2) (a b : ZMod 2) :
    Commute (observableToProjector O1 a) (observableToProjector O2 b) := by
  rw [observableToProjector, observableToProjector]
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (.one_left _)
  apply Commute.add_right (.one_right _)
  exact (h.smul_left _).smul_right _
end
end MIPRE.LCS

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- Jointly reading two commuting projective measurements gives a projective measurement. -/
theorem joint_measurement_isPVM {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (P : A → Matrix ι ι ℂ) (Q : B → Matrix ι ι ℂ) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ a b, Commute (P a) (Q b)) : IsPVM (fun ab : A × B => P ab.1 * Q ab.2) where
  isSelfAdjoint ab := by
    rw [Matrix.conjTranspose_mul, hP.isSelfAdjoint, hQ.isSelfAdjoint]
    exact (hc ab.1 ab.2).eq.symm
  idem ab := by
    rw [mul_assoc, ← mul_assoc (Q ab.2), (hc ab.1 ab.2).eq.symm,
      mul_assoc (P ab.1), hQ.idem, ← mul_assoc, hP.idem]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hQ.sum_eq_one, mul_one]
    exact hP.sum_eq_one
end
end MIPRE.Introspection

namespace MIPRE.Introspection.HonestMagicSquare
noncomputable section
open Matrix Finset LCS LCS.MagicSquare
open scoped Kronecker
variable {I : Type*} [Fintype I] [DecidableEq I]
theorem variableOp_isPVM {A B : Matrix I I ℂ}
    (hA : IsObservable A) (hB : IsObservable B) (hAB : A * B = -(B * A)) (j : Fin 9) :
    IsPVM (variableOp A B j) := by
  have h := isMeasurementSystem_observableToProjector _ (grid_isObservable hA hB hAB j)
  exact ⟨h.self_adjoint, h.idempotent, h.sum_one⟩
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
    (c : Fin layout.r) : IsPVM (constraintOp A B c) := by
  have hc (s t : Fin 3) (a b : ZMod 2) :
      Commute (variableOp A B (cellIndex c s) a) (variableOp A B (cellIndex c t) b) :=
    commute_observableToProjector (cells_commute hAB c s t) a b
  have h01 := joint_measurement_isPVM _ _ (variableOp_isPVM hA hB hAB (cellIndex c 0))
    (variableOp_isPVM hA hB hAB (cellIndex c 1)) (hc 0 1)
  have h012 := joint_measurement_isPVM _ _ h01 (variableOp_isPVM hA hB hAB (cellIndex c 2))
    (fun a b => (hc 0 2 a.1 b).mul_left (hc 1 2 a.2 b))
  refine ⟨fun a => h012.isSelfAdjoint (tripleEquiv a),
    fun a => h012.idem (tripleEquiv a), ?_⟩
  calc
    _ = ∑ a : (ZMod 2 × ZMod 2) × ZMod 2,
        (variableOp A B (cellIndex c 0) a.1.1 * variableOp A B (cellIndex c 1) a.1.2) *
          variableOp A B (cellIndex c 2) a.2 :=
      Fintype.sum_equiv tripleEquiv _ _ (fun _ => rfl)
    _ = 1 := h012.sum_eq_one
end MIPRE.Introspection.HonestMagicSquare
