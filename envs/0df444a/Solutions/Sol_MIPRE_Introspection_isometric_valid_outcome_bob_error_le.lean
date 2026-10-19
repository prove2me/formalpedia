-- Prove2me | solution 1 for MIPRE.Introspection.isometric_valid_outcome_bob_error_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:33:20.351978+00:00
-- url     : https://prove2.me/submissions/1878926e-04ef-494d-90f7-7730ebcb4fcf

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ValidOutcomeError.lean (solution of MIPRE.Introspection.isometric_valid_outcome_bob_error_le);
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy
import Theorems.Thm_MIPRE_Introspection_valid_outcome_error_le
import Theorems.Thm_MIPRE_POVM_sum_val

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_smul (c : ℂ) (X : Matrix HB HB ℂ) :
    bOp (c • X) = c • (bOp X : Matrix (HA × HB) _ ℂ) := Matrix.kronecker_smul _ _ _
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
theorem bOp_sub (X Y : Matrix HB HB ℂ) :
    bOp (X - Y) = (bOp X : Matrix (HA × HB) _ ℂ) - bOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, bOp_add, bOp_smul]
  module
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
theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
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
theorem bOp_nonneg {Y : Matrix HB HB ℂ} (hY : (0 : Matrix HB HB ℂ) ≤ Y) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ bOp Y :=
  Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.PosSemidef.one.kronecker (Matrix.nonneg_iff_posSemidef.mp hY))
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_mono {X Y : Matrix dB dB ℂ} (h : X ≤ Y) :
    (bOp X : Matrix (dA × dB) _ ℂ) ≤ bOp Y := by
  rw [← sub_nonneg, ← bOp_sub]
  exact bOp_nonneg (sub_nonneg.mpr h)
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
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **A projection is bounded by the identity.** -/
theorem proj_le_one {P : Matrix N N ℂ} (hsa : Pᴴ = P) (hidem : P * P = P) :
    P ≤ (1 : Matrix N N ℂ) := by
  refine sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
  have h : (1 : Matrix N N ℂ) - P = ((1 : Matrix N N ℂ) - P)ᴴ * ((1 : Matrix N N ℂ) - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_zero : (bOp (0 : Matrix dB dB ℂ) : Matrix (dA × dB) (dA × dB) ℂ) = 0 := by
  rw [bOp, Matrix.kronecker_zero]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
theorem IsPVM.bOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    IsPVM fun i => (bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [bOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← bOp_mul, h.idem]
  sum_eq_one := by rw [← bOp_sum, h.sum_eq_one, bOp_one]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {H R S : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
theorem isometricImage_nonneg (V : Matrix R H ℂ) {M : Matrix H H ℂ} (hM : 0 ≤ M) :
    0 ≤ isometricImage V M :=
  ((Matrix.nonneg_iff_posSemidef.mp hM).mul_mul_conjTranspose_same V).nonneg
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {H R S : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
theorem isometricImage_one_le (V : Matrix R H ℂ) (hV : Vᴴ * V = 1) :
    isometricImage V 1 ≤ 1 := by
  apply proj_le_one
  · rw [isometricImage_conjTranspose, Matrix.conjTranspose_one]
  · rw [isometricImage_mul V hV, Matrix.one_mul]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {H R S : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
theorem _root_.solution (V : Matrix S H ℂ) (hV : Vᴴ * V = 1)
    (ψ : R × S → ℂ) (hψ : ‖evec ψ‖ = 1) (M : POVM B H)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix S S ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ
      (bOp (isometricImage V (M.mats (v a)).val - P (some a))) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (bOp (isometricImage V ((M.map f).mats a).val - P a)) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by
  have hm b : 0 ≤ (bOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) :=
    bOp_nonneg (isometricImage_nonneg V (Subtype.coe_le_coe.mpr (M.nonneg b)))
  have hs : ∑ b, (bOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) ≤ 1 := by
    simp only [← bOp_sum, isometricImage, ← Matrix.mul_sum, ← Matrix.sum_mul, M.sum_val]
    exact (bOp_mono (isometricImage_one_le V hV)).trans_eq bOp_one
  have h := valid_outcome_error_le ψ hψ _ hm hs f v hv (fun a => bOp (P a)) hP.bOp
    (by rw [hPnone, bOp_zero]) (by simpa only [bOp_sub] using hclose)
  have he a : fibSum (fun b => (bOp (isometricImage V (M.mats b).val) :
      Matrix (R × S) _ ℂ)) f a = bOp (isometricImage V ((M.map f).mats a).val) := by
    rw [POVM.map_mats]
    simp only [fibSum, isometricImage, Matrix.mul_sum, Matrix.sum_mul, bOp_sum]
  simpa only [he, ← bOp_sub] using h
end MIPRE.Introspection
