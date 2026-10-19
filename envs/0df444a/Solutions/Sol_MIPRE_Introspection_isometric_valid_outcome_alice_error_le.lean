-- Prove2me | solution 1 for MIPRE.Introspection.isometric_valid_outcome_alice_error_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:34:51.250816+00:00
-- url     : https://prove2.me/submissions/590f0b79-ad8b-4da2-9467-15a0477494aa

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ValidOutcomeError.lean (solution of MIPRE.Introspection.isometric_valid_outcome_alice_error_le);
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
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_aOp_zero

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
theorem aOp_nonneg {X : Matrix HA HA ℂ} (hX : (0 : Matrix HA HA ℂ) ≤ X) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ aOp X :=
  Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp hX).kronecker (Matrix.PosSemidef.one))
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mono {X Y : Matrix dA dA ℂ} (h : X ≤ Y) :
    (aOp X : Matrix (dA × dB) _ ℂ) ≤ aOp Y := by
  rw [← sub_nonneg, ← aOp_sub]
  exact aOp_nonneg (sub_nonneg.mpr h)
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
theorem _root_.solution (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (ψ : R × S → ℂ) (hψ : ‖evec ψ‖ = 1) (M : POVM B H)
    (f : B → Option A) (v : A → B) (hv : ∀ a, f (v a) = some a)
    (P : Option A → Matrix R R ℂ) (hP : IsPVM P) (hPnone : P none = 0)
    {δ : ℝ} (hclose : ∑ a, snorm ψ
      (aOp (isometricImage V (M.mats (v a)).val - P (some a))) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (aOp (isometricImage V ((M.map f).mats a).val - P a)) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by
  have hm b : 0 ≤ (aOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) :=
    aOp_nonneg (isometricImage_nonneg V (Subtype.coe_le_coe.mpr (M.nonneg b)))
  have hs : ∑ b, (aOp (isometricImage V (M.mats b).val) : Matrix (R × S) _ ℂ) ≤ 1 := by
    simp only [← aOp_sum, isometricImage, ← Matrix.mul_sum, ← Matrix.sum_mul, M.sum_val]
    exact (aOp_mono (isometricImage_one_le V hV)).trans_eq aOp_one
  have h := valid_outcome_error_le ψ hψ _ hm hs f v hv (fun a => aOp (P a)) hP.aOp
    (by rw [hPnone, aOp_zero]) (by simpa only [aOp_sub] using hclose)
  have he a : fibSum (fun b => (aOp (isometricImage V (M.mats b).val) :
      Matrix (R × S) _ ℂ)) f a = aOp (isometricImage V ((M.map f).mats a).val) := by
    rw [POVM.map_mats]
    simp only [fibSum, isometricImage, Matrix.mul_sum, Matrix.sum_mul, aOp_sum]
  simpa only [he, ← aOp_sub] using h
end MIPRE.Introspection
