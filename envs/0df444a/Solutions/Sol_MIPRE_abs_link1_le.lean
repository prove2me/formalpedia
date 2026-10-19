-- Prove2me | solution 1 for MIPRE.abs_link1_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:31:41.903245+00:00
-- url     : https://prove2.me/submissions/fe75d82f-5dec-4529-94ef-84f78d088f0b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (solution of MIPRE.abs_link1_le);
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
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
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
/-- A bound in front of anything. -/
theorem snorm_mul_le {M : Matrix N N ℂ} {K : ℝ} (h : Bnd M K) (M' : Matrix N N ℂ) :
    snorm v (M * M') ≤ K * snorm v M' := by
  rw [snorm, snorm, ← Matrix.mulVec_mulVec]
  exact h (M' *ᵥ v)
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
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
/-- A contraction on the first factor is a contraction on the product space. -/
theorem bnd_aOp {X : Matrix HA HA ℂ} (h : (Xᴴ * X) ≤ (1 : Matrix HA HA ℂ)) :
    Bnd (aOp X : Matrix (HA × HB) _ ℂ) 1 := by
  refine bnd_one_of_conjTranspose_mul_self_le ?_
  rw [aOp_conjTranspose, ← aOp_mul, ← aOp_one (HA := HA) (HB := HB)]
  refine sub_nonneg.mp ?_
  rw [← aOp_sub]
  exact aOp_nonneg (sub_nonneg.mpr h)
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
omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl
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
omit [DecidableEq dB] in
theorem norm_stateVecB_eq_snorm (ψ : dA × dB → ℂ) (B : Matrix dB dB ℂ) :
    ‖stateVecB ψ B‖ = snorm ψ (bOp B : Matrix (dA × dB) _ ℂ) := rfl
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
/-- Cauchy--Schwarz for a mixed product, with the deviation on **Alice's** side. -/
theorem abs_qform_aOp_mul_bOp_le (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    |qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V)|
      ≤ ‖stateVecB ψ (Vᴴ)‖ * stateNorm ψ U := by
  have h : (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = (bOp (Vᴴ) : Matrix (dA × dB) _ ℂ)ᴴ * aOp U := by
    rw [bOp_conjTranspose, Matrix.conjTranspose_conjTranspose, aOp_mul_bOp]
  rw [h, stateNorm]
  refine le_trans (abs_qform_conjTranspose_mul_le ψ _ _) (le_of_eq ?_)
  rw [← norm_stateVecB_eq_snorm, ← norm_stateVec_eq_snorm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **A contraction in front costs nothing**, on Alice's side. -/
theorem stateNorm_mul_le (ψ : dA × dB → ℂ) {P : Matrix dA dA ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix dA dA ℂ)) (N : Matrix dA dA ℂ) :
    stateNorm ψ (P * N) ≤ stateNorm ψ N := by
  rw [stateNorm, stateNorm, norm_stateVec_eq_snorm, norm_stateVec_eq_snorm, aOp_mul]
  have h := snorm_mul_le ψ (bnd_aOp (HB := dB) hP) (aOp N : Matrix (dA × dB) _ ℂ)
  rwa [one_mul] at h
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
/-- A projective measurement's elements are contractions. -/
theorem IsPVM.conjTranspose_mul_self_le_one {N : Type*} [Fintype N] [DecidableEq N]
    {P : A → Matrix N N ℂ} (h : IsPVM P) (a : A) : (P a)ᴴ * P a ≤ (1 : Matrix N N ℂ) := by
  rw [h.isSelfAdjoint a, h.idem a]
  exact proj_le_one (h.isSelfAdjoint a) (h.idem a)
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
theorem _root_.solution (hZ : IsPVM Z) {S' : A × A → Matrix dB dB ℂ}
    (hS' : ∀ p, (S' p)ᴴ = S' p) :
    |(∑ p : A × A, qform ψ ((aOp (sand X Z p) : Matrix (dA × dB) _ ℂ) * bOp (S' p)))
        - ∑ p : A × A, qform ψ ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (S' p))|
      ≤ Real.sqrt (∑ p : A × A, stateSqNorm ψ (X p.1 * Z p.2 - Z p.2 * X p.1))
        * Real.sqrt (∑ p : A × A, ‖stateVecB ψ (S' p)‖ ^ 2) := by
  classical
  have hdiff : ∀ p : A × A, sand X Z p - Z p.2 * X p.1
      = Z p.2 * (X p.1 * Z p.2 - Z p.2 * X p.1) := by
    intro p
    calc sand X Z p - Z p.2 * X p.1
        = Z p.2 * X p.1 * Z p.2 - Z p.2 * Z p.2 * X p.1 := by rw [hZ.idem]; rfl
      _ = Z p.2 * (X p.1 * Z p.2 - Z p.2 * X p.1) := by noncomm_ring
  have hstep : (∑ p : A × A, qform ψ ((aOp (sand X Z p) : Matrix (dA × dB) _ ℂ) * bOp (S' p)))
        - ∑ p : A × A, qform ψ ((aOp (Z p.2 * X p.1) : Matrix (dA × dB) _ ℂ) * bOp (S' p))
      = ∑ p : A × A, qform ψ ((aOp (Z p.2 * (X p.1 * Z p.2 - Z p.2 * X p.1))
          : Matrix (dA × dB) _ ℂ) * bOp (S' p)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hdiff p, aOp_sub, Matrix.sub_mul, qform_sub]
  rw [hstep]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun p (_ : p ∈ univ) => ?_)
    (sum_mul_le_sqrt (fun p : A × A => stateNorm ψ (X p.1 * Z p.2 - Z p.2 * X p.1))
      (fun p : A × A => ‖stateVecB ψ (S' p)‖))
  refine le_trans (abs_qform_aOp_mul_bOp_le ψ _ _) (le_of_le_of_eq ?_ (mul_comm _ _))
  rw [hS' p]
  exact mul_le_mul_of_nonneg_left
    (stateNorm_mul_le (dB := dB) ψ (hZ.conjTranspose_mul_self_le_one p.2) _) (norm_nonneg _)
end MIPRE
