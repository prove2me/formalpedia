-- Prove2me | solution 1 for MIPRE.Introspection.retained_fibre_dist
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:15:50.534062+00:00
-- url     : https://prove2.me/submissions/d6dde41b-0e0b-4185-972c-a910c3cb7b26

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/RetainedFibre.lean (solution of MIPRE.Introspection.retained_fibre_dist);
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
import Theorems.Thm_MIPRE_IsPVM_marg_left
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le

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
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
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
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
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
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- **A contraction in front costs nothing.** The one-operator case of `sum_snorm_sq_mul_le`. -/
theorem snorm_sq_mul_le_of_contraction (v : N → ℂ) {P : Matrix N N ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix N N ℂ)) (M : Matrix N N ℂ) :
    snorm v (P * M) ^ 2 ≤ snorm v M ^ 2 := by
  rw [snorm_sq_eq_qform, snorm_sq_eq_qform, Matrix.conjTranspose_mul,
    show Mᴴ * Pᴴ * (P * M) = Mᴴ * (Pᴴ * P) * M from by noncomm_ring]
  refine qform_le_of_le v ?_
  have hpsd : (0 : Matrix N N ℂ) ≤ Mᴴ * ((1 : Matrix N N ℂ) - Pᴴ * P) * M :=
    Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hP)).conjTranspose_mul_mul_same M)
  rw [show Mᴴ * ((1 : Matrix N N ℂ) - Pᴴ * P) * M = Mᴴ * M - Mᴴ * (Pᴴ * P) * M from by
    noncomm_ring] at hpsd
  exact sub_nonneg.mp hpsd
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : P i - R i = (P i - Q i) + (Q i - R i) := by abel
  have htri : snorm v (P i - R i) ≤ snorm v (P i - Q i) + snorm v (Q i - R i) := by
    rw [hsplit]; exact snorm_add_le v _ _
  nlinarith [snorm_nonneg v (P i - Q i), snorm_nonneg v (Q i - R i),
    snorm_nonneg v (P i - R i), sq_nonneg (snorm v (P i - Q i) - snorm v (Q i - R i))]
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
theorem sum_prod_eq {M : Type*} [AddCommMonoid M] {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → M) : ∑ a, ∑ b, f a b = ∑ p : α × β, f p.1 p.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N Y A : Type*} [Fintype N] [DecidableEq N]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
/-- Multiplication on the right by a projector is contractive when it has a commuting mirror. -/
theorem snorm_right_projector_le (ψ : N → ℂ) (P R E : Matrix N N ℂ)
    (hRsa : Rᴴ = R) (hRid : R * R = R) (hPR : P *ᵥ ψ = R *ᵥ ψ)
    (hER : E * R = R * E) : snorm ψ (E * P) ^ 2 ≤ snorm ψ E ^ 2 := by
  have he : snorm ψ (E * P) = snorm ψ (R * E) := by
    rw [snorm, snorm, ← Matrix.mulVec_mulVec, hPR, Matrix.mulVec_mulVec, hER]
  rw [he]
  apply snorm_sq_mul_le_of_contraction
  rw [hRsa, hRid]
  exact proj_le_one hRsa hRid
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N Y A : Type*} [Fintype N] [DecidableEq N]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
/-- A joint PVM element is unchanged by multiplication by its own first marginal. -/
theorem joint_mul_marginal {M : Y × A → Matrix N N ℂ} (hM : IsPVM M) (y : Y) (a : A) :
    M (y, a) * (∑ b, M (y, b)) = M (y, a) := by
  rw [Finset.mul_sum]
  refine (Finset.sum_eq_single a ?_ ?_).trans (hM.idem (y, a))
  · intro b _ hba
    exact hM.orthogonal fun h => hba (Prod.mk.inj h).2.symm
  · intro h
    exact False.elim (h (mem_univ a))
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N Y A : Type*} [Fintype N] [DecidableEq N]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
theorem _root_.solution (ψ : N → ℂ) (M T : Y × A → Matrix N N ℂ)
    (P R : Y → Matrix N N ℂ) (hM : IsPVM M) (hR : IsPVM R)
    (hPR : ∀ y, P y *ᵥ ψ = R y *ᵥ ψ)
    (hMR : ∀ y a, M (y, a) * R y = R y * M (y, a))
    (hTR : ∀ y a, T (y, a) * R y = R y * T (y, a)) :
    (∑ p : Y × A, snorm ψ (M p - T p * P p.1) ^ 2) ≤
      2 * (∑ y, snorm ψ ((∑ a, M (y, a)) - P y) ^ 2) +
      2 * (∑ p : Y × A, snorm ψ (M p - T p) ^ 2) := by
  have hfirst y : (∑ a, snorm ψ (M (y, a) - M (y, a) * P y) ^ 2) ≤
      snorm ψ ((∑ a, M (y, a)) - P y) ^ 2 := by
    have hfamily : ∑ a, (M (y, a))ᴴ * M (y, a) ≤ (1 : Matrix N N ℂ) := by
      simp_rw [hM.isSelfAdjoint, hM.idem]
      exact proj_le_one (hM.marg_left.isSelfAdjoint y) (hM.marg_left.idem y)
    have he a : M (y, a) - M (y, a) * P y =
        M (y, a) * ((∑ b, M (y, b)) - P y) := by
      rw [mul_sub, joint_mul_marginal hM]
    simp_rw [he]
    exact sum_snorm_sq_mul_le ψ _ hfamily _
  have hfirstSum := Finset.sum_le_sum fun y (_ : y ∈ univ) => hfirst y
  rw [sum_prod_eq] at hfirstSum
  have hsecond : (∑ p : Y × A, snorm ψ (M p * P p.1 - T p * P p.1) ^ 2) ≤
      ∑ p : Y × A, snorm ψ (M p - T p) ^ 2 := by
    apply Finset.sum_le_sum
    intro p _
    rw [← sub_mul]
    apply snorm_right_projector_le ψ _ (R p.1) _ (hR.isSelfAdjoint p.1) (hR.idem p.1)
      (hPR p.1)
    rw [sub_mul, hMR p.1 p.2, hTR p.1 p.2, mul_sub]
  have htri := sum_snorm_sq_triangle' ψ M (fun p => M p * P p.1) (fun p => T p * P p.1)
  linarith
end MIPRE.Introspection
