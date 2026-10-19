-- Prove2me | solution 1 for MIPRE.sum_snorm_sq_comm_coarse_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:29:02.052561+00:00
-- url     : https://prove2.me/submissions/6b7f46c8-9d3f-47bd-9175-43f7288842ec

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.sum_snorm_sq_comm_coarse_le);
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
import Theorems.Thm_MIPRE_IsPVM_marg_right
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_commutation_analysis_abstract

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
variable (v : N → ℂ)
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
theorem xSqNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xSqNorm ψ A B := by rw [xSqNorm]; positivity
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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem sum_aOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι]
    {P : ι → Matrix dA dA ℂ} (h : IsPVM P) :
    ∑ i, ((aOp (P i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * aOp (P i) = 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by
      rw [aOp_conjTranspose, h.isSelfAdjoint, ← aOp_mul, h.idem],
    ← aOp_sum, h.sum_eq_one, aOp_one]
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
theorem _root_.solution {ψ : dA × dB → ℂ} {A : R1 × R2 → Matrix dA dA ℂ}
    {Gf : R2 → Matrix dB dB ℂ} (hA : IsPVM A) (hR : IsPVM R) (hGf : IsPVM Gf) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a) ≤ δ₁)
    (h2 : ∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (Gf b) ≤ δ₂) :
    ∑ a : R1, ∑ b : R2, snorm ψ (bOp (R a * Gf b - Gf b * R a) : Matrix (dA × dB) _ ℂ) ^ 2
      ≤ 16 * (δ₁ + δ₂) := by
  classical
  have hδ₂0 : 0 ≤ δ₂ := le_trans (Finset.sum_nonneg fun b _ => xSqNorm_nonneg _ _ _) h2
  have hδ₁0 : 0 ≤ δ₁ := le_trans (Finset.sum_nonneg fun a _ => xSqNorm_nonneg _ _ _) h1
  have hdev : ∀ (X : Matrix dA dA ℂ) (Y : Matrix dB dB ℂ),
      snorm ψ ((bOp Y : Matrix (dA × dB) _ ℂ) - aOp X) ^ 2 = xSqNorm ψ X Y := by
    intro X Y
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  have key := commutation_analysis_abstract (N := dA × dB) (B := R1) (C := R2) (δ := δ₁ + δ₂) ψ
    (fun a => (bOp (R a) : Matrix (dA × dB) _ ℂ))
    (fun b => (bOp (Gf b) : Matrix (dA × dB) _ ℂ))
    (fun a => (aOp (∑ b : R2, A (a, b)) : Matrix (dA × dB) _ ℂ))
    (fun b => (aOp (∑ a : R1, A (a, b)) : Matrix (dA × dB) _ ℂ))
    (fun p => (aOp (A p) : Matrix (dA × dB) _ ℂ))
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hR))
    (le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hGf))
    (le_of_eq (sum_aOp_conjTranspose_mul_self_of_isPVM hA.marg_left))
    (le_of_eq (sum_aOp_conjTranspose_mul_self_of_isPVM hA.marg_right))
    (fun a b => (aOp_mul_bOp _ _).symm) (fun b a => (aOp_mul_bOp _ _).symm)
    (fun a b => by rw [← aOp_mul, hA.marg_mul_marg a b])
    (fun a b => by rw [← aOp_mul, hA.marg_mul_marg' a b])
    (by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hdev (∑ b : R2, A (a, b)) (R a)]
      linarith)
    (by
      rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hdev (∑ a : R1, A (a, b)) (Gf b)]
      linarith)
  rw [sum_prod_eq fun (a : R1) (b : R2) =>
    snorm ψ (bOp (R a * Gf b - Gf b * R a) : Matrix (dA × dB) _ ℂ) ^ 2]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) key
  rw [bOp_sub, bOp_mul, bOp_mul]
end MIPRE
