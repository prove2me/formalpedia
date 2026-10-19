-- Prove2me | solution 1 for MIPRE.abs_sand_sub_ord_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:31:41.328687+00:00
-- url     : https://prove2.me/submissions/1f140ca0-bb18-46dd-b84a-738409a0eaa4

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.abs_sand_sub_ord_le);
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
import Theorems.Thm_MIPRE_IsPVM_orthogonal
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
variable (v : N → ℂ)
theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  rw [qform, qform, qform, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
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
    {A : R1 × R2 → Matrix dA dA ℂ} (hA : IsPVM A) (hG : IsPVM G) (e : K → R2) :
    |(∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a)|
      ≤ Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) := by
  classical
  have hterm : ∀ (a : R1) (g : K),
      bornProb ψ (A (a, e g)) (G g * R a * G g) - bornProb ψ (A (a, e g)) (G g * R a)
        = qform ψ (((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g))ᴴ
            * bOp (R a * G g - G g * R a)) := by
    intro a g
    have hM : ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g))ᴴ
          * bOp (R a * G g - G g * R a)
        = (aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g * R a * G g)
          - (aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g * R a) := by
      rw [aOp_bOp_conjTranspose, hA.isSelfAdjoint, hG.isSelfAdjoint,
        Matrix.mul_assoc (aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ), ← bOp_mul,
        show G g * (R a * G g - G g * R a) = G g * R a * G g - G g * R a from by
          rw [Matrix.mul_sub, show G g * (G g * R a) = G g * G g * R a from by noncomm_ring,
            hG.idem, Matrix.mul_assoc],
        bOp_sub, Matrix.mul_sub]
    rw [hM, qform_sub, bornProb_eq_qform, bornProb_eq_qform]
  have hsum : (∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a * G g))
        - ∑ a : R1, ∑ g : K, bornProb ψ (A (a, e g)) (G g * R a)
      = ∑ a : R1, ∑ g : K, qform ψ (((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g))ᴴ
          * bOp (R a * G g - G g * R a)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hterm a g
  rw [hsum]
  have hmass : ∑ a : R1, ∑ g : K,
      snorm ψ ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g)) ^ 2 ≤ 1 :=
    sum_snorm_sq_prod_le_one hψ (fun a g => A (a, e g)) G
      (fun a g => hA.isSelfAdjoint _) (fun a g => hA.idem _)
      (fun a a' g hne => hA.orthogonal fun h => hne (Prod.ext_iff.mp h).1) hG
  refine le_trans (abs_sum_sum_le_sqrt _
    (fun a g => snorm ψ ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g)))
    (fun a g => snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ))
    fun a g => abs_qform_conjTranspose_mul_le ψ _ _) ?_
  calc Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ ((aOp (A (a, e g)) : Matrix (dA × dB) _ ℂ) * bOp (G g)) ^ 2)
        * Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ Real.sqrt 1 * Real.sqrt (∑ a : R1, ∑ g : K,
          snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_one, one_mul]
end MIPRE
