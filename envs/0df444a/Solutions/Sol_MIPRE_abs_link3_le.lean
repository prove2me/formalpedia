-- Prove2me | solution 1 for MIPRE.abs_link3_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:33:45.352915+00:00
-- url     : https://prove2.me/submissions/7020f50e-9da3-420e-adfc-dab8ef3b0fcb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (solution of MIPRE.abs_link3_le);
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
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := norm_nonneg _
end
end MIPRE

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
theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  rw [qform, qform, qform, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
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
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_one [DecidableEq N] (hv : ‖evec v‖ = 1) : qform v (1 : Matrix N N ℂ) = 1 := by
  rw [qform, Matrix.one_mulVec, ← norm_evec_sq, hv, one_pow]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
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
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem qform_nonneg_of_nonneg (v : N → ℂ) {Z : Matrix N N ℂ}
    (hZ : (0 : Matrix N N ℂ) ≤ Z) : 0 ≤ qform v Z := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hZ).dotProduct_mulVec_nonneg v
  exact (Complex.nonneg_iff.mp h).1
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem qform_le_of_le (v : N → ℂ) {X Y : Matrix N N ℂ} (h : X ≤ Y) :
    qform v X ≤ qform v Y := by
  have h0 : 0 ≤ qform v (Y - X) := qform_nonneg_of_nonneg v (sub_nonneg.mpr h)
  rw [qform_sub] at h0
  linarith
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
theorem inner_evec (u w : N → ℂ) : (inner ℂ (evec u) (evec w) : ℂ) = star u ⬝ᵥ w := by
  rw [evec, evec, EuclideanSpace.inner_toLp_toLp, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
/-- **Cauchy--Schwarz for a quadratic form.** The one estimate the chain uses, in the shape the
chain needs: the form of a product, split onto the two vectors. -/
theorem abs_qform_conjTranspose_mul_le (v : N → ℂ) (M P : Matrix N N ℂ) :
    |qform v (Mᴴ * P)| ≤ snorm v M * snorm v P := by
  have h : qform v (Mᴴ * P) = (inner ℂ (evec (M *ᵥ v)) (evec (P *ᵥ v)) : ℂ).re := by
    rw [qform, ← star_mulVec_dotProduct, inner_evec]
  rw [h]
  exact le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
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
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **A projection is a contraction on a unit vector.** -/
theorem snorm_le_one_of_proj {v : N → ℂ} (hv : ‖evec v‖ = 1) {P : Matrix N N ℂ}
    (hsa : Pᴴ = P) (hidem : P * P = P) : snorm v P ≤ 1 := by
  have hsq : snorm v P ^ 2 ≤ 1 := by
    rw [snorm_sq_eq_qform, hsa, hidem]
    refine le_trans (qform_le_of_le v (proj_le_one hsa hidem)) ?_
    rw [qform_one v hv]
  nlinarith [snorm_nonneg v P, hsq]
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
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- **A sum of mutually orthogonal projections is a projection.** -/
theorem conjTranspose_sum_of_orth {ι : Type*} [Fintype ι] {P : ι → Matrix N N ℂ}
    (hsa : ∀ i, (P i)ᴴ = P i) : (∑ i, P i)ᴴ = ∑ i, P i := by
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => hsa i
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem mul_self_sum_of_orth {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Matrix N N ℂ}
    (hidem : ∀ i, P i * P i = P i) (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    (∑ i, P i) * (∑ i, P i) = ∑ i, P i := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i (mem_univ i)
    fun j _ hj => horth i j (Ne.symm hj)]
  exact hidem i
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_bOp_mul_aOp_bOp (U U' : Matrix dA dA ℂ) (V V' : Matrix dB dB ℂ) :
    ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) * ((aOp U' : Matrix (dA × dB) _ ℂ) * bOp V')
      = (aOp (U * U') : Matrix (dA × dB) _ ℂ) * bOp (V * V') := by
  rw [aOp_mul_bOp_eq, aOp_mul_bOp_eq, aOp_mul_bOp_eq, ← Matrix.mul_kronecker_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_bOp_conjTranspose (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V)ᴴ
      = (aOp (Uᴴ) : Matrix (dA × dB) _ ℂ) * bOp (Vᴴ) := by
  rw [aOp_mul_bOp_eq, aOp_mul_bOp_eq, Matrix.conjTranspose_kronecker]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}
/-- The diagonal `Z`-agreement operator, and the `X`-disagreement operator: both projections,
because their summands are mutually orthogonal projections. -/
theorem isProj_diag (hZ : IsPVM Z) (hZ' : IsPVM Z') :
    ((∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))ᴴ
        = ∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
      ∧ (∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
          * (∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
        = ∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b) := by
  refine ⟨conjTranspose_sum_of_orth fun b => ?_, mul_self_sum_of_orth (fun b => ?_) fun b b' hb => ?_⟩
  · rw [aOp_bOp_conjTranspose, hZ.isSelfAdjoint, hZ'.isSelfAdjoint]
  · rw [aOp_bOp_mul_aOp_bOp, hZ.idem, hZ'.idem]
  · rw [aOp_bOp_mul_aOp_bOp, hZ'.orthogonal hb, bOp, Matrix.kronecker_zero, Matrix.mul_zero]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}
theorem isProj_disag (hX : IsPVM X) (hX' : IsPVM X') :
    ((∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))ᴴ
        = ∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
      ∧ (∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
          * (∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
        = ∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a) := by
  have hsa : ∀ a : A, ((1 : Matrix dA dA ℂ) - X a)ᴴ = 1 - X a := fun a => by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX.isSelfAdjoint]
  have hid : ∀ a : A, ((1 : Matrix dA dA ℂ) - X a) * (1 - X a) = 1 - X a := fun a => by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hX.idem]
    abel
  refine ⟨conjTranspose_sum_of_orth fun a => ?_, mul_self_sum_of_orth (fun a => ?_) fun a a' ha => ?_⟩
  · rw [aOp_bOp_conjTranspose, hsa, hX'.isSelfAdjoint]
  · rw [aOp_bOp_mul_aOp_bOp, hid, hX'.idem]
  · rw [aOp_bOp_mul_aOp_bOp, hX'.orthogonal ha, bOp, Matrix.kronecker_zero, Matrix.mul_zero]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}
/-- The `X`-disagreement operator's expectation is the `X`-consistency defect. -/
theorem qform_disag (hψ : ‖evec ψ‖ = 1) (hX : IsPVM X) (hX' : IsPVM X') :
    qform ψ (∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a))
      = (∑ a : A, xSqNorm ψ (X a) (X' a)) / 2 := by
  classical
  have hterm : ∀ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a)
      = (bOp (X' a) : Matrix (dA × dB) _ ℂ) - (aOp (X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a) := by
    intro a
    rw [aOp_sub, aOp_one, Matrix.sub_mul, Matrix.one_mul]
  have hone : ∑ a : A, qform ψ (bOp (X' a) : Matrix (dA × dB) _ ℂ) = 1 := by
    rw [← qform_sum, ← bOp_sum, hX'.sum_eq_one, bOp_one, qform_one _ hψ]
  rw [qform_sum, Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
      rw [hterm a, qform_sub, ← bornProb_eq_qform], Finset.sum_sub_distrib, hone,
    ← one_sub_sum_bornProb_eq hψ hX hX']
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}
theorem _root_.solution (hψ : ‖evec ψ‖ = 1) (hX : IsPVM X) (hZ : IsPVM Z)
    (hX' : IsPVM X') (hZ' : IsPVM Z') :
    |(∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1)))
        - ∑ p : A × A, qform ψ
          ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))|
      ≤ Real.sqrt ((∑ a : A, xSqNorm ψ (X a) (X' a)) / 2) := by
  classical
  set Pd : Matrix (dA × dB) (dA × dB) ℂ :=
    ∑ b : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b) with hPd
  set Dd : Matrix (dA × dB) (dA × dB) ℂ :=
    ∑ a : A, (aOp (1 - X a) : Matrix (dA × dB) _ ℂ) * bOp (X' a) with hDd
  have hprod : Pd * Dd = ∑ p : A × A, (aOp (Z p.2 * (1 - X p.1)) : Matrix (dA × dB) _ ℂ)
      * bOp (Z' p.2 * X' p.1) := by
    rw [sum_prod_swap (fun p : A × A => (aOp (Z p.2 * (1 - X p.1)) : Matrix (dA × dB) _ ℂ)
      * bOp (Z' p.2 * X' p.1)), hPd, hDd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => aOp_bOp_mul_aOp_bOp _ _ _ _
  rw [abs_sub_comm]
  have hstep : (∑ p : A × A, qform ψ
          ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1)))
        - ∑ p : A × A, qform ψ
          ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))
      = qform ψ (Pd * Dd) := by
    rw [hprod, qform_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← qform_sub]
    congr 1
    rw [Matrix.mul_sub, Matrix.mul_one, aOp_sub, Matrix.sub_mul]
  rw [hstep]
  have hPsa := (isProj_diag (dB := dB) hZ hZ').1
  have hPid := (isProj_diag (dB := dB) hZ hZ').2
  have hDsa := (isProj_disag (dB := dB) hX hX').1
  have hDid := (isProj_disag (dB := dB) hX hX').2
  have hcs : |qform ψ (Pd * Dd)| ≤ snorm ψ Pd * snorm ψ Dd := by
    have h := abs_qform_conjTranspose_mul_le ψ Pd Dd
    rwa [hPsa] at h
  have hP1 : snorm ψ Pd ≤ 1 := snorm_le_one_of_proj hψ hPsa hPid
  have hDeq : snorm ψ Dd = Real.sqrt ((∑ a : A, xSqNorm ψ (X a) (X' a)) / 2) := by
    rw [← qform_disag hψ hX hX', ← hDd,
      show qform ψ Dd = snorm ψ Dd ^ 2 from by rw [snorm_sq_eq_qform, hDsa, hDid],
      Real.sqrt_sq (snorm_nonneg ψ Dd)]
  rw [← hDeq]
  calc |qform ψ (Pd * Dd)| ≤ snorm ψ Pd * snorm ψ Dd := hcs
    _ ≤ 1 * snorm ψ Dd := mul_le_mul_of_nonneg_right hP1 (snorm_nonneg ψ Dd)
    _ = snorm ψ Dd := one_mul _
end MIPRE
