-- Prove2me | solution 1 for MIPRE.Introspection.conditional_coarse_overlap
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:45.954116+00:00
-- url     : https://prove2.me/submissions/e4ea0918-41e3-491d-9408-52c3e31405c5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ConditionalNormalizer.lean (solution of MIPRE.Introspection.conditional_coarse_overlap);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Theorems.Thm_MIPRE_IsPVM_posSemidef
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_bornProb_nonneg

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_add (M M' : Matrix N N ℂ) : qform v (M + M') = qform v M + qform v M' := by
  rw [qform, qform, qform, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix N N ℂ) :
    qform v (∑ i ∈ s, f i) = ∑ i ∈ s, qform v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qform]
  | insert i s hi ih => rw [Finset.sum_insert hi, qform_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dB dB ℂ) :
    bOp (∑ i ∈ s, f i) = ∑ i ∈ s, (bOp (f i) : Matrix (dA × dB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bOp, Matrix.kronecker_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, bOp_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mul_bOp_eq (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = U ⊗ₖ V := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_eq_qform (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    bornProb ψ U V = qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) := by
  rw [aOp_mul_bOp_eq, bornProb, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sum_left {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : ι → Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    bornProb ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, bornProb ψ (A i) B := by
  rw [bornProb_eq_qform, aOp_sum, Finset.sum_mul, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ (A i) B).symm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sum_right {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι)
    (A : Matrix dA dA ℂ) (B : ι → Matrix dB dB ℂ) :
    bornProb ψ A (∑ i ∈ s, B i) = ∑ i ∈ s, bornProb ψ A (B i) := by
  rw [bornProb_eq_qform, bOp_sum, Finset.mul_sum, qform_sum]
  exact Finset.sum_congr rfl fun i _ => (bornProb_eq_qform ψ A (B i)).symm
end
end MIPRE

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]
theorem _root_.solution (ψ : H × K → ℂ)
    (M : I → Matrix H H ℂ) (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hM : IsPVM M) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) :
    (∑ i, bornProb ψ (M i) (P i)) ≤
      ∑ p : Y × Z, bornProb ψ (fibSum M (f p.1) p.2) (conditionalIdeal P Q f p) := by
  have hjoint := joint_measurement_isPVM Q P hQ hP hc
  have hfib (y : Y) (z : Z) :
      bornProb ψ (fibSum M (f y) z) (conditionalIdeal P Q f (y, z)) =
        ∑ i ∈ univ.filter (fun i => f y i = z),
          ∑ j ∈ univ.filter (fun j => f y j = z), bornProb ψ (M i) (Q y * P j) := by
    simp only [conditionalIdeal, fibSum, Finset.mul_sum]
    rw [bornProb_sum_left]
    exact Finset.sum_congr rfl fun i _ => bornProb_sum_right ψ _ _ _
  have hdiag (y : Y) (z : Z) :
      (∑ i ∈ univ.filter (fun i => f y i = z), bornProb ψ (M i) (Q y * P i)) ≤
        bornProb ψ (fibSum M (f y) z) (conditionalIdeal P Q f (y, z)) := by
    rw [hfib]
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.single_le_sum
      (fun j _ => bornProb_nonneg ψ (hM.posSemidef i) (hjoint.posSemidef (y, j))) hi
  have hsum (y : Y) :
      (∑ i, bornProb ψ (M i) (Q y * P i)) ≤
        ∑ z, bornProb ψ (fibSum M (f y) z) (conditionalIdeal P Q f (y, z)) := by
    calc
      _ = ∑ z, ∑ i ∈ univ.filter (fun i => f y i = z),
          bornProb ψ (M i) (Q y * P i) := (Finset.sum_fiberwise _ _ _).symm
      _ ≤ _ := Finset.sum_le_sum fun z _ => hdiag y z
  have hrecover : (∑ y, ∑ i, bornProb ψ (M i) (Q y * P i)) =
      ∑ i, bornProb ψ (M i) (P i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← bornProb_sum_right, ← Finset.sum_mul, hQ.sum_eq_one, one_mul]
  rw [← hrecover, Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun y _ => hsum y
end MIPRE.Introspection
