-- Prove2me | solution 1 for MIPRE.abs_sigma_sub_cloud_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:32:01.220782+00:00
-- url     : https://prove2.me/submissions/06d1589f-4329-40ce-a3c0-159b1eb9b646

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.abs_sigma_sub_cloud_le);
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
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl
end
end MIPRE

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
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **`X² ≤ X` for `0 ≤ X ≤ 1`**: `X - X² = X (1 - X)` is a product of commuting positive
matrices. -/
theorem mul_self_le_of_le_one {X : Matrix N N ℂ} (h0 : (0 : Matrix N N ℂ) ≤ X)
    (h1 : X ≤ (1 : Matrix N N ℂ)) : X * X ≤ X := by
  have hc : Commute X ((1 : Matrix N N ℂ) - X) := by
    show X * (1 - X) = (1 - X) * X
    noncomm_ring
  have hprod : (0 : Matrix N N ℂ) ≤ X * (1 - X) := hc.mul_nonneg h0 (sub_nonneg.mpr h1)
  have heq : X * ((1 : Matrix N N ℂ) - X) = X - X * X := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod
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
theorem bOp_nonneg {Y : Matrix HB HB ℂ} (hY : (0 : Matrix HB HB ℂ) ≤ Y) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ bOp Y :=
  Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.PosSemidef.one.kronecker (Matrix.nonneg_iff_posSemidef.mp hY))
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
theorem xSqNorm_eq_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = xNorm ψ A B ^ 2 := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The deviation is the state-norm of the single operator `A ⊗ Id - Id ⊗ B` on the product
space, which is what the operator-norm calculus of `MIPRE/Foundations/OpBound.lean` consumes. -/
theorem xNorm_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) _ ℂ) - bOp B) := by
  rw [xNorm, snorm, Matrix.sub_mulVec, evec_sub]
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The squared cross-party deviation as a `snorm` on the joint space, which is the form the
chains of the appendix are run in. -/
theorem xSqNorm_eq_snorm_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) (dA × dB) ℂ) - bOp B) ^ 2 := by
  rw [xSqNorm_eq_sq, xNorm_eq_snorm]
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
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- An unweighted Cauchy--Schwarz, in the same shape. -/
theorem sum_mul_le_sqrt {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    ∑ i, u i * v i ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  have h := sum_weighted_mul_le_sqrt (fun _ : ι => (1 : ℝ)) u v fun _ => zero_le_one
  simpa using h
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
/-- A positive operator below the identity has `M^2 <= M`, so a family of positive operators
summing to the identity has its squares summing to at most the identity. -/
theorem sum_sq_le_one_of_sum_eq_one {C : Type*} [Fintype C] {P : C → Matrix N N ℂ}
    (hP0 : ∀ c, (0 : Matrix N N ℂ) ≤ P c) (hPsum : ∑ c, P c = 1) :
    ∑ c, (P c) * (P c) ≤ (1 : Matrix N N ℂ) := by
  classical
  have hP1 : ∀ c, P c ≤ (1 : Matrix N N ℂ) := fun c =>
    le_trans (Finset.single_le_sum (fun c' _ => hP0 c') (mem_univ c)) (le_of_eq hPsum)
  calc ∑ c, (P c) * (P c) ≤ ∑ c, P c :=
        Finset.sum_le_sum fun c _ => mul_self_le_of_le_one (hP0 c) (hP1 c)
    _ = 1 := hPsum
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
theorem sum_prod_eq {M : Type*} [AddCommMonoid M] {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → M) : ∑ a, ∑ b, f a b = ∑ p : α × β, f p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- **Cauchy--Schwarz for a double sum**, in the shape the steps use: each term is dominated by a
product, and the two factors separate. -/
theorem abs_sum_sum_le_sqrt {α β : Type*} [Fintype α] [Fintype β] (f u v : α → β → ℝ)
    (hf : ∀ a b, |f a b| ≤ u a b * v a b) :
    |∑ a, ∑ b, f a b| ≤ Real.sqrt (∑ a, ∑ b, u a b ^ 2) * Real.sqrt (∑ a, ∑ b, v a b ^ 2) := by
  rw [sum_prod_eq f, sum_prod_eq fun a b => u a b ^ 2, sum_prod_eq fun a b => v a b ^ 2]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact le_trans (Finset.sum_le_sum fun p _ => hf p.1 p.2)
    (sum_mul_le_sqrt (fun p : α × β => u p.1 p.2) fun p : α × β => v p.1 p.2)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- **A POVM**: each square is below the element, and the elements sum to the identity. -/
theorem sum_snorm_sq_povm_le_one {ι : Type*} [Fintype ι] {v : N → ℂ} (hv : ‖evec v‖ = 1)
    {P : ι → Matrix N N ℂ} (hP0 : ∀ i, (0 : Matrix N N ℂ) ≤ P i) (hPsum : ∑ i, P i = 1) :
    ∑ i, snorm v (P i) ^ 2 ≤ 1 := by
  have hsa : ∀ i, (P i)ᴴ = P i := fun i => (Matrix.nonneg_iff_posSemidef.mp (hP0 i)).isHermitian
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by rw [snorm_sq_eq_qform, hsa i],
    ← qform_sum, ← qform_one v hv]
  exact qform_le_of_le v (sum_sq_le_one_of_sum_eq_one hP0 hPsum)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
/-- Each term of the pasting sandwich is a Gram operator, hence positive. -/
theorem sandOp_posSemidef (hR : IsPVM R) (hG : IsPVM G) (a : R1) (g : K) :
    (R a * G g * R a).PosSemidef := by
  have h : R a * G g * R a = (G g * R a)ᴴ * (G g * R a) := by
    calc R a * G g * R a = R a * (G g * G g) * R a := by rw [hG.idem]
      _ = (G g * R a)ᴴ * (G g * R a) := by
          rw [Matrix.conjTranspose_mul, hR.isSelfAdjoint, hG.isSelfAdjoint]; noncomm_ring
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
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
/-- The pasting sandwich is a POVM: the inner family sums away against `R`'s projectivity. -/
theorem sum_sandOp (hR : IsPVM R) (hG : IsPVM G) :
    ∑ p : R1 × K, R p.1 * G p.2 * R p.1 = 1 := by
  rw [← sum_prod_eq fun (a : R1) (g : K) => R a * G g * R a]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => show
      (∑ g : K, R a * G g * R a) = R a from by
        rw [show (∑ g : K, R a * G g * R a) = R a * (∑ g : K, G g) * R a from by
          rw [Matrix.mul_sum, Finset.sum_mul], hG.sum_eq_one, Matrix.mul_one, hR.idem],
    hR.sum_eq_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
/-- The squared state norms of the pasting sandwich sum to at most one. -/
theorem sum_snorm_sq_sandOp_le_one {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) (hR : IsPVM R)
    (hG : IsPVM G) :
    ∑ a : R1, ∑ g : K,
        snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2 ≤ 1 := by
  rw [sum_prod_eq fun (a : R1) (g : K) =>
    snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2]
  refine sum_snorm_sq_povm_le_one hψ
    (fun p => bOp_nonneg (Matrix.nonneg_iff_posSemidef.mpr (sandOp_posSemidef hR hG p.1 p.2))) ?_
  rw [← bOp_sum, sum_sandOp hR hG, bOp_one]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {Ga : K → Matrix dA dA ℂ}
    (hR : IsPVM R) (hG : IsPVM G) :
    |(∑ a : R1, ∑ g : K, qform ψ (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)|
      ≤ Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) := by
  classical
  have hsa : ∀ (a : R1) (g : K),
      ((bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))ᴴ = bOp (R a * G g * R a) := by
    intro a g
    rw [bOp_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hR.isSelfAdjoint, hG.isSelfAdjoint, Matrix.mul_assoc]
  -- the one matrix identity: an `R a` in front of the deviation is free, because the sandwich
  -- already ends in `R a`
  have hM : ∀ (a : R1) (g : K), (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ)
        * ((bOp (R a) : Matrix (dA × dB) _ ℂ)
          * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g)))
      = (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ)
        - aOp (Ga g) * bOp (R a * G g * R a) := by
    intro a g
    have hRR : R a * G g * R a * R a = R a * G g * R a := by
      rw [show R a * G g * R a * R a = R a * G g * (R a * R a) from by noncomm_ring, hR.idem]
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← bOp_mul,
      ← bOp_mul, hRR, ← aOp_mul_bOp]
  have hterm : ∀ (a : R1) (g : K),
      qform ψ (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ)
          - bornProb ψ (Ga g) (R a * G g * R a)
        = qform ψ (((bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))ᴴ
            * ((bOp (R a) : Matrix (dA × dB) _ ℂ)
              * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g)))) := by
    intro a g
    rw [hsa a g, hM a g, qform_sub, bornProb_eq_qform]
  have hsum : (∑ a : R1, ∑ g : K,
        qform ψ (bOp (R a * G g * R a * G g) : Matrix (dA × dB) _ ℂ))
        - ∑ a : R1, ∑ g : K, bornProb ψ (Ga g) (R a * G g * R a)
      = ∑ a : R1, ∑ g : K, qform ψ (((bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))ᴴ
          * ((bOp (R a) : Matrix (dA × dB) _ ℂ)
            * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hterm a g
  rw [hsum]
  -- the two mass bounds, then Cauchy--Schwarz
  have hmass1 := sum_snorm_sq_sandOp_le_one (dA := dA) hψ hR hG
  have hmass2 : ∑ a : R1, ∑ g : K, snorm ψ ((bOp (R a) : Matrix (dA × dB) _ ℂ)
        * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))) ^ 2
      ≤ ∑ g : K, xSqNorm ψ (Ga g) (G g) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun g _ => ?_
    refine le_trans (sum_snorm_sq_mul_le ψ (fun a => (bOp (R a) : Matrix (dA × dB) _ ℂ))
      (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hR))
      ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))) ?_
    refine le_of_eq ?_
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  refine le_trans (abs_sum_sum_le_sqrt _
    (fun a g => snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ))
    (fun a g => snorm ψ ((bOp (R a) : Matrix (dA × dB) _ ℂ)
      * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))))
    fun a g => abs_qform_conjTranspose_mul_le ψ _ _) ?_
  calc Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2)
        * Real.sqrt (∑ a : R1, ∑ g : K, snorm ψ ((bOp (R a) : Matrix (dA × dB) _ ℂ)
          * ((bOp (G g) : Matrix (dA × dB) _ ℂ) - aOp (Ga g))) ^ 2)
      ≤ Real.sqrt 1 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) :=
        mul_le_mul (Real.sqrt_le_sqrt hmass1) (Real.sqrt_le_sqrt hmass2)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) := by rw [Real.sqrt_one, one_mul]
end MIPRE
