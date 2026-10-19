-- Prove2me | solution 1 for MIPRE.commutation_analysis
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:42.470185+00:00
-- url     : https://prove2.me/submissions/ae3a5ecf-cc90-4718-8068-6c1f00d7e76b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (solution of MIPRE.commutation_analysis);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
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
import Theorems.Thm_MIPRE_IsPVM_marg_left
import Theorems.Thm_MIPRE_IsPVM_marg_right
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_commutation_analysis_abstract

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
/-- **The two factors commute.** -/
theorem aOp_mul_bOp (X : Matrix HA HA ℂ) (Y : Matrix HB HB ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ) * bOp Y = bOp Y * aOp X := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
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
theorem aOp_nonneg {X : Matrix HA HA ℂ} (hX : (0 : Matrix HA HA ℂ) ≤ X) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ aOp X :=
  Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp hX).kronecker (Matrix.PosSemidef.one))
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
/-- Each POVM element is at most the identity. -/
theorem POVM.le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (p : A) : ((M.mats p).val) ≤ (1 : Matrix d d ℂ) := by
  rw [← POVM.sum_val M]
  exact Finset.single_le_sum (fun a _ => Subtype.coe_le_coe.mpr (M.nonneg a)) (Finset.mem_univ p)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- `A² ≤ A` for a POVM element: `A^{1/2}(1 - A)A^{1/2} ≥ 0`, here through the commuting
product `A * (1 - A)`. -/
theorem POVM.mul_self_le_self (M : POVM A dA) (a : A) :
    ((M.mats a).val) * ((M.mats a).val) ≤ ((M.mats a).val) := by
  set P := ((M.mats a).val) with hP
  have h0 : (0 : Matrix dA dA ℂ) ≤ P := Subtype.coe_le_coe.mpr (M.nonneg a)
  have h1 : (0 : Matrix dA dA ℂ) ≤ 1 - P := sub_nonneg.mpr (M.le_one a)
  have hc : Commute P (1 - P) := by show P * (1 - P) = (1 - P) * P; noncomm_ring
  have hprod : (0 : Matrix dA dA ℂ) ≤ P * (1 - P) := hc.mul_nonneg h0 h1
  have heq : P * ((1 : Matrix dA dA ℂ) - P) = P - P * P := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod
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
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **A POVM on Alice's factor satisfies the hypothesis of `sum_snorm_sq_mul_le`.** No
projectivity: `A^dag A = A^2 <= A` and the elements sum to one. -/
theorem sum_aOp_conjTranspose_mul_self_le_one {ι : Type*} [Fintype ι] (A : POVM ι dA) :
    ∑ i, ((aOp ((A.mats i).val) : Matrix (dA × dB) _ ℂ))ᴴ * aOp ((A.mats i).val)
      ≤ (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  have hterm : ∀ i : ι, ((aOp ((A.mats i).val) : Matrix (dA × dB) _ ℂ))ᴴ
      * aOp ((A.mats i).val) = aOp ((A.mats i).val * (A.mats i).val) := by
    intro i
    rw [aOp_conjTranspose, ← aOp_mul, ← Matrix.star_eq_conjTranspose, (A.mats i).2]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← aOp_sum,
    ← aOp_one (HA := dA) (HB := dB)]
  refine aOp_mono ?_
  rw [← POVM.sum_val A]
  exact Finset.sum_le_sum fun i _ => POVM.mul_self_le_self A i
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- A projective family on Bob's factor satisfies the hypothesis of `sum_snorm_sq_mul_le` with
equality. -/
theorem sum_bOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    ∑ i, ((bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * bOp (Q i)
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  have hterm : ∀ i : ι, ((bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * bOp (Q i)
      = bOp (Q i) := by
    intro i
    rw [bOp_conjTranspose, ← bOp_mul, h.isSelfAdjoint, h.idem]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← bOp_sum, h.sum_eq_one, bOp_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N B C : Type*} [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
/-- **The two marginals of a projective measurement multiply to the joint element.** This is the
whole use of projectivity in the commutation analysis: the off-diagonal terms of the product
vanish by `IsPVM.orthogonal`, and the surviving one is idempotent. -/
theorem IsPVM.marg_mul_marg {P : B × C → Matrix N N ℂ} (h : IsPVM P) (b : B) (c : C) :
    (∑ b', P (b', c)) * (∑ c', P (b, c')) = P (b, c) := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single b (fun b' _ hb' => ?_) fun hmem => absurd (Finset.mem_univ b) hmem]
  · rw [Finset.mul_sum,
      Finset.sum_eq_single c (fun c' _ hc' => ?_) fun hmem => absurd (Finset.mem_univ c) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2.symm
  · rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun c' _ => ?_
    exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N B C : Type*} [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
/-- The other order. -/
theorem IsPVM.marg_mul_marg' {P : B × C → Matrix N N ℂ} (h : IsPVM P) (b : B) (c : C) :
    (∑ c', P (b, c')) * (∑ b', P (b', c)) = P (b, c) := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single c (fun c' _ hc' => ?_) fun hmem => absurd (Finset.mem_univ c) hmem]
  · rw [Finset.mul_sum,
      Finset.sum_eq_single b (fun b' _ hb' => ?_) fun hmem => absurd (Finset.mem_univ b) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hb' (Prod.mk.injEq .. ▸ he).1.symm
  · rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun b' _ => ?_
    exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
theorem _root_.solution {ψ : dA × dB → ℂ} {A : POVM B dA} {Cm : POVM C dA}
    {P : B × C → Matrix dB dB ℂ} (hP : IsPVM P) {δ : ℝ}
    (hA : ∑ b, snorm ψ ((aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ c, P (b, c))) ^ 2 ≤ δ)
    (hC : ∑ c, snorm ψ ((aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ b, P (b, c))) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm ψ ((aOp ((A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((Cm.mats p.2).val)
        - (aOp ((Cm.mats p.2).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((A.mats p.1).val)) ^ 2 ≤ 16 * δ :=
  commutation_analysis_abstract ψ
    (fun b => (aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun c => (aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun b => (bOp (∑ c, P (b, c)) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun c => (bOp (∑ b, P (b, c)) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun p => (bOp (P p) : Matrix (dA × dB) (dA × dB) ℂ))
    (sum_aOp_conjTranspose_mul_self_le_one A) (sum_aOp_conjTranspose_mul_self_le_one Cm)
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hP.marg_left))
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hP.marg_right))
    (fun b c => aOp_mul_bOp _ _) (fun b c => aOp_mul_bOp _ _)
    (fun b c => by rw [← bOp_mul, hP.marg_mul_marg b c])
    (fun b c => by rw [← bOp_mul, hP.marg_mul_marg' b c])
    hA hC
end MIPRE
