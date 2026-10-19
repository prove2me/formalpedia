-- Prove2me | solution 1 for MIPRE.sum_bornProb_ord_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:32:58.968989+00:00
-- url     : https://prove2.me/submissions/975004f8-f3e9-4b51-87f1-ec40500cd44f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.sum_bornProb_ord_ge);
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
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_IsPVM_marg_left
import Theorems.Thm_MIPRE_IsPVM_marg_right
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_eq
import Theorems.Thm_MIPRE_sum_snorm_sq_prod_le_one
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

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
variable {N B C : Type*} [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
/-- The marginal over `C`, as the coarse-graining of `P` that forgets the second outcome. -/
theorem IsPVM.sum_marg_left {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    ∑ b, (∑ c, P (b, c)) = 1 := by
  rw [← Fintype.sum_prod_type]
  exact h.sum_eq_one
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
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e
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
/-- A sum whose summand depends on the index only through its image splits into the fibres. -/
theorem sum_fiber {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (e : α → β) (f : β → α → M) :
    ∑ g : α, f (e g) g = ∑ b : β, ∑ g ∈ univ.filter fun g => e g = b, f b g := by
  classical
  conv_lhs => rw [← Finset.sum_fiberwise (univ : Finset α) e fun g => f (e g) g]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g hg => by
    rw [(Finset.mem_filter.mp hg).2]
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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_sub_right (ψ : dA × dB → ℂ) (X : Matrix dA dA ℂ) (M N : Matrix dB dB ℂ) :
    bornProb ψ X (M - N) = bornProb ψ X M - bornProb ψ X N := by
  rw [bornProb_eq_qform, bornProb_eq_qform, bornProb_eq_qform, bOp_sub, Matrix.mul_sub, qform_sub]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- A product of two commuting projections is a projection, so its squared state norm is its
quadratic form --- a Born probability. -/
theorem snorm_sq_prod_proj (ψ : dA × dB → ℂ) {P : Matrix dA dA ℂ} {Q : Matrix dB dB ℂ}
    (hPsa : Pᴴ = P) (hPi : P * P = P) (hQsa : Qᴴ = Q) (hQi : Q * Q = Q) :
    snorm ψ ((aOp P : Matrix (dA × dB) _ ℂ) * bOp Q) ^ 2
      = bornProb ψ P Q := by
  rw [snorm_sq_eq_qform, aOp_bOp_conjTranspose, hPsa, hQsa, aOp_bOp_mul_aOp_bOp, hPi, hQi,
    bornProb_eq_qform]
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
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R) (hG : IsPVM G) (e : K → R2) :
    1 - (∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b)) / 2
        - Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2)
      ≤ ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a) := by
  classical
  -- the split `G_g R_a = G_g - G_g (Id - R_a)`
  have hsplit : ∀ (a : R1) (g : K), bornProb ψ (A (a, e g)) (G g * R a)
      = bornProb ψ (A (a, e g)) (G g)
        - bornProb ψ (A (a, e g)) (G g * ((1 : Matrix dB dB ℂ) - R a)) := by
    intro a g
    rw [← bornProb_sub_right,
      show G g - G g * ((1 : Matrix dB dB ℂ) - R a) = G g * R a from by
        rw [Matrix.mul_sub, Matrix.mul_one]; abel]
  -- the first term is the `G`-consistency of Alice's second marginal
  have hterm1 : ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g)
      = 1 - (∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b)) / 2 := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun g (_ : g ∈ univ) => (bornProb_sum_left ψ univ
        (fun a => A (a, e g)) (G g)).symm,
      sum_fiber e fun b g => bornProb ψ (∑ a : R1, A (a, b)) (G g),
      Finset.sum_congr rfl fun b (_ : b ∈ univ) => show
        (∑ g ∈ univ.filter fun g => e g = b, bornProb ψ (∑ a : R1, A (a, b)) (G g))
          = bornProb ψ (∑ a : R1, A (a, b)) (fibSum G e b) from
        (bornProb_sum_right ψ (univ.filter fun g => e g = b) (∑ a : R1, A (a, b)) G).symm]
    have h := one_sub_sum_bornProb_eq (dA := dA) (dB := dB) hψ hA.marg_right (isPVM_fibSum hG e)
    linarith
  -- the second term is bounded by the square root of the `R`-consistency
  have hbar : ((1 : Matrix dB dB ℂ) - R ·) = fun a => (1 : Matrix dB dB ℂ) - R a := rfl
  have hbarsa : ∀ a : R1, ((1 : Matrix dB dB ℂ) - R a)ᴴ = (1 : Matrix dB dB ℂ) - R a := by
    intro a
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hR.isSelfAdjoint]
  have hbari : ∀ a : R1, ((1 : Matrix dB dB ℂ) - R a) * ((1 : Matrix dB dB ℂ) - R a)
      = (1 : Matrix dB dB ℂ) - R a := by
    intro a
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hR.idem]
    abel
  -- regrouping the second term along the fibres of `e`
  have hterm2eq : ∀ a : R1, ∑ g : K, bornProb ψ (A (a, e g))
        (G g * ((1 : Matrix dB dB ℂ) - R a))
      = ∑ b : R2, bornProb ψ (A (a, b)) (fibSum G e b * ((1 : Matrix dB dB ℂ) - R a)) := by
    intro a
    rw [sum_fiber e fun b g => bornProb ψ (A (a, b)) (G g * ((1 : Matrix dB dB ℂ) - R a))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [fibSum, Finset.sum_mul, bornProb_sum_right]
  have hCS : ∀ (a : R1) (b : R2),
      |bornProb ψ (A (a, b)) (fibSum G e b * ((1 : Matrix dB dB ℂ) - R a))|
        ≤ snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b))
          * snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
            * bOp ((1 : Matrix dB dB ℂ) - R a)) := by
    intro a b
    have hM : ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b))ᴴ
          * ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp ((1 : Matrix dB dB ℂ) - R a))
        = (aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
          * bOp (fibSum G e b * ((1 : Matrix dB dB ℂ) - R a)) := by
      rw [aOp_bOp_conjTranspose, hA.isSelfAdjoint,
        (isPVM_fibSum hG e).isSelfAdjoint, aOp_bOp_mul_aOp_bOp, hA.idem]
    have h := abs_qform_conjTranspose_mul_le ψ
      ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b))
      ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp ((1 : Matrix dB dB ℂ) - R a))
    rw [hM, ← bornProb_eq_qform] at h
    exact h
  have hmass1 : ∑ a : R1, ∑ b : R2,
      snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b)) ^ 2 ≤ 1 :=
    sum_snorm_sq_prod_le_one hψ (fun a b => A (a, b)) (fibSum G e)
      (fun a b => hA.isSelfAdjoint _) (fun a b => hA.idem _)
      (fun a a' b hne => hA.orthogonal fun h => hne (Prod.ext_iff.mp h).1) (isPVM_fibSum hG e)
  have hmass2 : ∑ a : R1, ∑ b : R2, snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
        * bOp ((1 : Matrix dB dB ℂ) - R a)) ^ 2
      = (∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2 := by
    have hone : ∑ a : R1, bornProb ψ (∑ b : R2, A (a, b)) (1 : Matrix dB dB ℂ) = 1 := by
      have hsum : ∑ a : R1, (∑ b : R2, A (a, b)) = 1 := hA.sum_marg_left
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => bornProb_eq_qform ψ _ _, ← qform_sum]
      rw [show (∑ a : R1, (aOp (∑ b : R2, A (a, b)) : Matrix (dA × dB) _ ℂ)
            * bOp (1 : Matrix dB dB ℂ))
          = (1 : Matrix (dA × dB) (dA × dB) ℂ) from by
        simp only [bOp_one, Matrix.mul_one]
        rw [← aOp_sum, hsum, aOp_one], qform_one _ hψ]
    have hsq : ∀ (a : R1) (b : R2), snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
          * bOp ((1 : Matrix dB dB ℂ) - R a)) ^ 2
        = bornProb ψ (A (a, b)) ((1 : Matrix dB dB ℂ) - R a) := fun a b =>
      snorm_sq_prod_proj ψ (hA.isSelfAdjoint _) (hA.idem _) (hbarsa a) (hbari a)
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      Finset.sum_congr rfl fun b (_ : b ∈ univ) => hsq a b]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      (bornProb_sum_left ψ univ (fun b => A (a, b)) ((1 : Matrix dB dB ℂ) - R a)).symm]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      bornProb_sub_right ψ (∑ b : R2, A (a, b)) 1 (R a), Finset.sum_sub_distrib, hone]
    have h := one_sub_sum_bornProb_eq (dA := dA) (dB := dB) hψ hA.marg_left hR
    linarith
  -- assembling
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun g (_ : g ∈ univ) => hsplit a g]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => Finset.sum_sub_distrib _ _,
    Finset.sum_sub_distrib, hterm1]
  have hbound : ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g))
        (G g * ((1 : Matrix dB dB ℂ) - R a))
      ≤ Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2) := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hterm2eq a]
    refine le_trans (le_abs_self _) (le_trans (abs_sum_sum_le_sqrt _
      (fun a b => snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b)))
      (fun a b => snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ)
        * bOp ((1 : Matrix dB dB ℂ) - R a))) fun a b => hCS a b) ?_)
    rw [hmass2]
    calc Real.sqrt (∑ a : R1, ∑ b : R2,
            snorm ψ ((aOp (A (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (fibSum G e b)) ^ 2)
          * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2)
        ≤ Real.sqrt 1 * Real.sqrt ((∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a)) / 2) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmass1) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, one_mul]
  linarith
end MIPRE
