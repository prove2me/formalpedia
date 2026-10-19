-- Prove2me | solution 1 for MIPRE.condFail_le_of
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:29.988403+00:00
-- url     : https://prove2.me/submissions/3e042e0c-243e-4410-9b82-cadb3cfbefaf

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Disagreement.lean (solution of MIPRE.condFail_le_of);
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
import Theorems.Thm_MIPRE_dis_map_eq_sum
import Theorems.Thm_MIPRE_sum_bornProb

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
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1) {x : X} {y : Y} (EA : A → Prop) (EB : B → Prop)
    [DecidablePred EA] [DecidablePred EB] (f : A → C) (g : B → C)
    (hD : ∀ a b, ¬ EA a → ¬ EB b → f a = g b → G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
        + ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
        + dis ψ ((MA x).map f) ((MB y).map g) := by
  have hβ0 : ∀ a b, 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := fun a b =>
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  have htot := sum_bornProb hψ (MA x) (MB y)
  have hfail : condFail G ψ MA MB x y
      = ∑ a, ∑ b, (if G.D x y a b then 0 else 1)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    have hsum : ∑ a, ∑ b, (if G.D x y a b then (0 : ℝ) else 1)
          * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)
        + condWin G ψ MA MB x y
        = ∑ a, ∑ b, bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
      unfold condWin
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    unfold condFail
    linarith
  have hA : ∑ a, (if EA a then bornProb ψ (((MA x).mats a).val) (1 : Matrix dB dB ℂ) else 0)
      = ∑ a, ∑ b, (if EA a then 1 else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · simp only [one_mul]; exact bornProb_one_right ψ _ (MB y)
    · simp
  have hB : ∑ b, (if EB b then bornProb ψ (1 : Matrix dA dA ℂ) (((MB y).mats b).val) else 0)
      = ∑ a, ∑ b, (if EB b then 1 else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp only [one_mul]; exact bornProb_one_left ψ (MA x) _
    · simp
  rw [hfail, hA, hB, dis_map_eq_sum hψ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have h0 := hβ0 a b
  by_cases hd : G.D x y a b = true
  · have e1 : 0 ≤ (if EA a then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have e2 : 0 ≤ (if EB b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
    rw [if_pos hd, zero_mul]
    positivity
  · rw [if_neg hd, one_mul]
    by_cases ha : EA a
    · have e2 : 0 ≤ (if EB b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
      rw [if_pos ha, one_mul]
      nlinarith
    · by_cases hb : EB b
      · have e3 : 0 ≤ (if f a = g b then (0 : ℝ) else 1) := by split_ifs <;> norm_num
        rw [if_neg ha, if_pos hb, zero_mul, one_mul, zero_add]
        nlinarith
      · have hfg : f a ≠ g b := fun h => hd (hD a b ha hb h)
        rw [if_neg ha, if_neg hb, if_neg hfg]
        simp
end MIPRE
