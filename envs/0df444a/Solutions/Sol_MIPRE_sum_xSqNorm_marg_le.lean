-- Prove2me | solution 1 for MIPRE.sum_xSqNorm_marg_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:32:21.869129+00:00
-- url     : https://prove2.me/submissions/bbbacfd5-379f-4db8-83a4-1e9eda3435ac

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.sum_xSqNorm_marg_le);
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
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_snorm_sq_sum_proj_mul
import Theorems.Thm_MIPRE_sum_snorm_sq_cool

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
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
theorem IsPVM.bOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    IsPVM fun i => (bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [bOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← bOp_mul, h.idem]
  sum_eq_one := by rw [← bOp_sum, h.sum_eq_one, bOp_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
theorem sum_fibre_fst {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [AddCommMonoid M]
    (i : ι) (g : ι × κ → M) :
    ∑ p ∈ univ.filter fun p : ι × κ => p.1 = i, g p = ∑ k : κ, g (i, k) := by
  classical
  rw [show (univ.filter fun p : ι × κ => p.1 = i) = ({i} : Finset ι) ×ˢ (univ : Finset κ) from by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true], Finset.sum_product, Finset.sum_singleton]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
/-- `sum_snorm_sq_cool` at the fibres of the first projection of a product outcome set. -/
theorem sum_snorm_sq_cool_prod {N : Type*} [Fintype N] [DecidableEq N] (v : N → ℂ)
    {A : R1 × R2 → Matrix N N ℂ} (hA : IsPVM A) (B : R1 × R2 → Matrix N N ℂ) :
    ∑ a : R1, snorm v (∑ b : R2, (A (a, b) - A (a, b) * B (a, b))) ^ 2
      ≤ ∑ p : R1 × R2, snorm v (A p - B p) ^ 2 := by
  classical
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    (sum_snorm_sq_cool v hA B Prod.fst)
  exact congrArg (fun M => snorm v M ^ 2)
    (sum_fibre_fst a fun p => A p - A p * B p).symm
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
theorem _root_.solution {ψ : dA × dB → ℂ} {Q : R1 × R2 → Matrix dA dA ℂ}
    {Z : R2 → Matrix dB dB ℂ} (X : R1 → Matrix dB dB ℂ) (hQ : IsPVM Q) (hZ : IsPVM Z) :
    ∑ a : R1, xSqNorm ψ (∑ b : R2, Q (a, b)) (X a)
      ≤ 2 * (∑ p : R1 × R2, snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
              - aOp (Q p)) ^ 2)
        + 2 * ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
  classical
  -- the intermediate operator: the marginal with Bob's projection attached
  have hcool : ∑ a : R1, snorm ψ ((aOp (∑ b : R2, Q (a, b)) : Matrix (dA × dB) _ ℂ)
        - ∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b)) ^ 2
      ≤ ∑ p : R1 × R2, snorm ψ ((aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2)
          - aOp (Q p)) ^ 2 := by
    have h := sum_snorm_sq_cool_prod (ψ) hQ.aOp
      (fun p => (aOp (Q p) : Matrix (dA × dB) _ ℂ) * bOp (Z p.2))
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (le_trans h
      (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)))
    · refine congrArg (fun M => snorm ψ M ^ 2) ?_
      rw [aOp_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ)
          * ((aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b))
          = (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b) from by
        rw [← Matrix.mul_assoc, ← aOp_mul, hQ.idem]]
    · rw [snorm_sub_comm]
  -- the orthogonal insertion
  have horth : ∑ a : R1, snorm ψ ((∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b))
        - bOp (X a)) ^ 2
      ≤ ∑ p : R1 × R2, xSqNorm ψ (Q p) (Z p.2 * X p.1) := by
    have hsplit : ∀ a : R1, (∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b))
          - bOp (X a)
        = ∑ b : R2, (bOp (Z b) : Matrix (dA × dB) _ ℂ)
            * ((aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) - bOp (Z b * X a)) := by
      intro a
      rw [show (bOp (X a) : Matrix (dA × dB) _ ℂ) = ∑ b : R2, (bOp (Z b * X a)) from by
        rw [← bOp_sum, ← Finset.sum_mul, hZ.sum_eq_one, Matrix.one_mul],
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_sub, ← aOp_mul_bOp, ← bOp_mul,
        show Z b * (Z b * X a) = Z b * X a from by
          rw [show Z b * (Z b * X a) = Z b * Z b * X a from by noncomm_ring, hZ.idem]]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      congrArg (fun M => snorm ψ M ^ 2) (hsplit a)]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
      snorm_sq_sum_proj_mul ψ (fun b => hZ.bOp.isSelfAdjoint b)
        (fun b b' hbb' => hZ.bOp.orthogonal hbb') _ univ]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    rw [xSqNorm_eq_snorm_sq]
    refine snorm_sq_mul_le_of_contraction ψ ?_ _
    rw [hZ.bOp.isSelfAdjoint, hZ.bOp.idem]
    exact proj_le_one (hZ.bOp.isSelfAdjoint b) (hZ.bOp.idem b)
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    xSqNorm_eq_snorm_sq ψ (∑ b : R2, Q (a, b)) (X a)]
  refine le_trans (sum_snorm_sq_triangle' ψ _
    (fun a => ∑ b : R2, (aOp (Q (a, b)) : Matrix (dA × dB) _ ℂ) * bOp (Z b)) _) ?_
  linarith
end MIPRE
