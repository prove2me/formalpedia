-- Prove2me | solution 1 for MIPRE.sum_ite_bornProb_one_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:14.956034+00:00
-- url     : https://prove2.me/submissions/d49ca3f3-360d-4d06-8575-a72305e523a0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Disagreement.lean (solution of MIPRE.sum_ite_bornProb_one_le);
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_Disagreement
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_dis_eq_sum_ne

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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_nonneg (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg ψ)).1
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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem bornProb_one_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (N : POVM Λ dB) :
    bornProb ψ EA (1 : Matrix dB dB ℂ) = ∑ b, bornProb ψ EA ((N.mats b).val) := by
  rw [← POVM.sum_val N, bornProb_sum_right]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem bornProb_one_left (ψ : dA × dB → ℂ) (M : POVM Λ dA) (EB : Matrix dB dB ℂ) :
    bornProb ψ (1 : Matrix dA dA ℂ) EB = ∑ a, bornProb ψ ((M.mats a).val) EB := by
  rw [← POVM.sum_val M, bornProb_sum_left]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) [DecidableEq Λ]
    (M : POVM Λ dA) (N : POVM Λ dB) (E : Λ → Prop) [DecidablePred E] :
    ∑ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ ∑ b, (if E b then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats b).val) else 0)
        + dis ψ M N := by
  have h0 : ∀ a b, 0 ≤ bornProb ψ ((M.mats a).val) ((N.mats b).val) := fun a b =>
    bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)
  rw [dis_eq_sum_ne hψ]
  -- Alice's side: the diagonal plus the off-diagonal
  have hA : ∀ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ (if E a then bornProb ψ ((M.mats a).val) ((N.mats a).val) else 0)
        + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
    intro a
    rw [bornProb_one_right ψ _ N]
    have hsplit : ∑ b, bornProb ψ ((M.mats a).val) ((N.mats b).val)
        = bornProb ψ ((M.mats a).val) ((N.mats a).val)
          + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _
        (Finset.mem_univ a), if_pos rfl, zero_add]
      congr 1
      exact Finset.sum_congr rfl fun b hb => by rw [if_neg (Finset.ne_of_mem_erase hb).symm]
    have hoff : 0 ≤ ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val) :=
      Finset.sum_nonneg fun b _ => by split_ifs <;> simp [h0 a b]
    split_ifs
    · rw [hsplit]
    · linarith
  -- Bob's side: the diagonal is at most Bob's marginal
  have hB : ∀ a, (if E a then bornProb ψ ((M.mats a).val) ((N.mats a).val) else 0)
      ≤ (if E a then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats a).val) else 0) := by
    intro a
    split_ifs
    · rw [bornProb_one_left ψ M]
      exact Finset.single_le_sum (f := fun a' => bornProb ψ ((M.mats a').val) ((N.mats a).val))
        (fun a' _ => h0 a' a) (Finset.mem_univ a)
    · exact le_rfl
  calc ∑ a, (if E a then bornProb ψ ((M.mats a).val) (1 : Matrix dB dB ℂ) else 0)
      ≤ ∑ a, ((if E a then bornProb ψ ((M.mats a).val) ((N.mats a).val) else 0)
        + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val)) :=
        Finset.sum_le_sum fun a _ => hA a
    _ ≤ ∑ a, ((if E a then bornProb ψ (1 : Matrix dA dA ℂ) ((N.mats a).val) else 0)
        + ∑ b, if a = b then 0 else bornProb ψ ((M.mats a).val) ((N.mats b).val)) :=
        Finset.sum_le_sum fun a _ => by linarith [hB a]
    _ = _ := Finset.sum_add_distrib
end MIPRE
