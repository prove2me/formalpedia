-- Prove2me | solution 1 for MIPRE.sum_snorm_sq_comm_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:28:58.759548+00:00
-- url     : https://prove2.me/submissions/1cce1fc7-1152-42d9-b07b-3c5cd0798231

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.sum_snorm_sq_comm_eq);
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
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem dotProduct_star_comm (u w : N → ℂ) : star u ⬝ᵥ w = star (star w ⬝ᵥ u) := by
  rw [dotProduct, dotProduct, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul']
  simp [Pi.star_apply, mul_comm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The quadratic form does not see the adjoint: it is a real part, and the adjoint conjugates. -/
theorem qform_conjTranspose (v : N → ℂ) (M : Matrix N N ℂ) : qform v (Mᴴ) = qform v M := by
  have h0 := star_mulVec_dotProduct M (1 : Matrix N N ℂ) v
  rw [Matrix.mul_one, Matrix.one_mulVec] at h0
  rw [qform, qform, ← h0, dotProduct_star_comm (M *ᵥ v) v, RCLike.star_def, Complex.conj_re,
    dotProduct_star_comm v (M *ᵥ v), RCLike.star_def, Complex.conj_re]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Z Y G2 R1 R2 : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype G2] [DecidableEq G2] [Fintype R1] [DecidableEq R1]
  [Fintype R2] [DecidableEq R2]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 → Matrix dB dB ℂ} {B : G2 → Matrix dB dB ℂ} (hA : IsPVM A) (hB : IsPVM B) :
    ∑ a : R1, ∑ g : G2, snorm ψ (bOp (A a * B g - B g * A a) : Matrix (dA × dB) _ ℂ) ^ 2
      = 2 - 2 * ∑ a : R1, ∑ g : G2,
          qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ) := by
  classical
  -- the expansion of one squared deviation
  have hterm : ∀ (a : R1) (g : G2),
      snorm ψ (bOp (A a * B g - B g * A a) : Matrix (dA × dB) _ ℂ) ^ 2
        = qform ψ (bOp (A a * B g * A a) : Matrix (dA × dB) _ ℂ)
          + qform ψ (bOp (B g * A a * B g) : Matrix (dA × dB) _ ℂ)
          - qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ)
          - qform ψ (bOp (B g * A a * B g * A a) : Matrix (dA × dB) _ ℂ) := by
    intro a g
    rw [snorm_sq_eq_qform, bOp_conjTranspose, ← bOp_mul,
      show (A a * B g - B g * A a)ᴴ * (A a * B g - B g * A a)
          = A a * B g * A a + B g * A a * B g
            - A a * B g * A a * B g - B g * A a * B g * A a from by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hA.isSelfAdjoint, hB.isSelfAdjoint]
        calc (B g * A a - A a * B g) * (A a * B g - B g * A a)
            = B g * (A a * A a) * B g + A a * (B g * B g) * A a
              - B g * A a * B g * A a - A a * B g * A a * B g := by noncomm_ring
          _ = _ := by rw [hA.idem, hB.idem]; abel,
      bOp_sub, bOp_sub, bOp_add, qform_sub, qform_sub, qform_add]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) =>
    Finset.sum_congr rfl fun g (_ : g ∈ univ) => hterm a g]
  -- the two diagonal sums are exactly one, and the two off-diagonal sums are equal
  have h1 : ∑ a : R1, ∑ g : G2,
      qform ψ (bOp (A a * B g * A a) : Matrix (dA × dB) _ ℂ) = 1 := by
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => by
        rw [← qform_sum, ← bOp_sum,
          show (∑ g : G2, A a * B g * A a) = A a * A a from by
            rw [show (∑ g : G2, A a * B g * A a) = A a * (∑ g : G2, B g) * A a from by
              rw [Matrix.mul_sum, Finset.sum_mul], hB.sum_eq_one, Matrix.mul_one], hA.idem],
      ← qform_sum, ← bOp_sum, hA.sum_eq_one, bOp_one, qform_one _ hψ]
  have h2 : ∑ a : R1, ∑ g : G2,
      qform ψ (bOp (B g * A a * B g) : Matrix (dA × dB) _ ℂ) = 1 := by
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun g (_ : g ∈ univ) => by
        rw [← qform_sum, ← bOp_sum,
          show (∑ a : R1, B g * A a * B g) = B g * B g from by
            rw [show (∑ a : R1, B g * A a * B g) = B g * (∑ a : R1, A a) * B g from by
              rw [Matrix.mul_sum, Finset.sum_mul], hA.sum_eq_one, Matrix.mul_one], hB.idem],
      ← qform_sum, ← bOp_sum, hB.sum_eq_one, bOp_one, qform_one _ hψ]
  have h3 : ∑ a : R1, ∑ g : G2,
      qform ψ (bOp (B g * A a * B g * A a) : Matrix (dA × dB) _ ℂ)
        = ∑ a : R1, ∑ g : G2,
          qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun g _ => ?_
    have hadj : (A a * B g * A a * B g)ᴴ = B g * A a * B g * A a := by
      simp only [Matrix.conjTranspose_mul, hA.isSelfAdjoint, hB.isSelfAdjoint]
      noncomm_ring
    rw [← qform_conjTranspose ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ),
      bOp_conjTranspose, hadj]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1, h2, h3]
  ring
end MIPRE
