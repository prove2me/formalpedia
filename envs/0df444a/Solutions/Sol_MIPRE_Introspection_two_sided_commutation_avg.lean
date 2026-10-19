-- Prove2me | solution 1 for MIPRE.Introspection.two_sided_commutation_avg
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:43.053075+00:00
-- url     : https://prove2.me/submissions/7c85684d-4c85-4524-a235-56fa9e51e0e6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwoSidedCommutation.lean (solution of MIPRE.Introspection.two_sided_commutation_avg);
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
import Theorems.Thm_MIPRE_Introspection_commutator_product_bound
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum

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
/-- An isometry on the first factor is an isometry on the product space. -/
theorem isometry_aOp {X : Matrix HA HA ℂ} (h : Xᴴ * X = 1) :
    ((aOp X : Matrix (HA × HB) _ ℂ))ᴴ * aOp X = 1 := by
  rw [aOp_conjTranspose, ← aOp_mul, h, aOp_one]
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
theorem isometry_bOp {Y : Matrix HB HB ℂ} (h : Yᴴ * Y = 1) :
    ((bOp Y : Matrix (HA × HB) _ ℂ))ᴴ * bOp Y = 1 := by
  rw [bOp_conjTranspose, ← bOp_mul, h, bOp_one]
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

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- The bipartite version: `W` is the second party's mirror of Alice's `V`. -/
theorem two_sided_commutation (ψ : dA × dB → ℂ) (M : POVM A dA)
    (U V : Matrix dA dA ℂ) (W : Matrix dB dB ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) :
    (∑ a, stateSqNorm ψ ((M.mats a).val * (U * V) - (U * V) * (M.mats a).val)) ≤
      4 * (∑ a, stateSqNorm ψ ((M.mats a).val * U - U * (M.mats a).val)) +
      4 * (∑ a, stateSqNorm ψ ((M.mats a).val * V - V * (M.mats a).val)) +
      8 * xSqNorm ψ V W := by
  have h := commutator_product_bound ψ (fun a => aOp ((M.mats a).val))
    (sum_aOp_conjTranspose_mul_self_le_one M) (aOp U) (aOp V) (bOp W)
    (isometry_aOp hU) (isometry_bOp hW)
    (aOp_mul_bOp U W).symm (fun a => (aOp_mul_bOp _ W).symm)
  simpa only [← aOp_mul, ← aOp_sub, ← xSqNorm_eq_snorm_sq,
    stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using h
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (μ : X → I → ℝ) (ν : X → J → ℝ)
    (hμ0 : ∀ x i, 0 ≤ μ x i) (hν0 : ∀ x j, 0 ≤ ν x j)
    (hμ1 : ∀ x, ∑ i, μ x i = 1) (hν1 : ∀ x, ∑ j, ν x j = 1)
    (ψ : dA × dB → ℂ) (M : X → POVM A dA)
    (U : X → I → Matrix dA dA ℂ) (V : X → J → Matrix dA dA ℂ)
    (W : X → J → Matrix dB dB ℂ)
    (hU : ∀ x i, (U x i)ᴴ * U x i = 1) (hW : ∀ x j, (W x j)ᴴ * W x j = 1) :
    (∑ x, D x * ∑ i, μ x i * ∑ j, ν x j * ∑ a,
      stateSqNorm ψ (((M x).mats a).val * (U x i * V x j) -
        (U x i * V x j) * ((M x).mats a).val)) ≤
      4 * (∑ x, D x * ∑ i, μ x i * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * U x i - U x i * ((M x).mats a).val)) +
      4 * (∑ x, D x * ∑ j, ν x j * ∑ a,
        stateSqNorm ψ (((M x).mats a).val * V x j - V x j * ((M x).mats a).val)) +
      8 * (∑ x, D x * ∑ j, ν x j * xSqNorm ψ (V x j) (W x j)) := by
  have hpoint x i j := two_sided_commutation ψ (M x) (U x i) (V x j) (W x j)
    (hU x i) (hW x j)
  calc
    _ ≤ ∑ x, D x * ∑ i, μ x i * ∑ j, ν x j *
        (4 * (∑ a, stateSqNorm ψ (((M x).mats a).val * U x i -
          U x i * ((M x).mats a).val)) +
        4 * (∑ a, stateSqNorm ψ (((M x).mats a).val * V x j -
          V x j * ((M x).mats a).val)) + 8 * xSqNorm ψ (V x j) (W x j)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hD x)
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hμ0 x i)
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint x i j) (hν0 x j)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      have hconst (x : X) (r : ℝ) : (∑ j, ν x j * r) = r := by
        rw [← Finset.sum_mul, hν1, one_mul]
      have hconst' (x : X) (r : ℝ) : (∑ i, μ x i * r) = r := by
        rw [← Finset.sum_mul, hμ1, one_mul]
      simp_rw [hconst, hconst']
      simp only [mul_left_comm (b := (4 : ℝ)), mul_left_comm (b := (8 : ℝ)),
        ← Finset.mul_sum]
end MIPRE.Introspection
