-- Prove2me | solution 1 for MIPRE.sum_dis_triangle
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:31.466482+00:00
-- url     : https://prove2.me/submissions/449aebc9-e396-4814-84dc-f273436ab0f3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Disagreement.lean (solution of MIPRE.sum_dis_triangle);
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
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_Disagreement
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_sum_bornProb
import Theorems.Thm_MIPRE_sum_snorm_sq_triangle3
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one
import Theorems.Thm_MIPRE_weightA_ge
import Theorems.Thm_MIPRE_weightB_ge
import Theorems.Thm_MIPRE_xDev_eq

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
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
theorem stateVecB_entry (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) (i : dA) (j : dB) :
    (((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ) (i, j) = ∑ l, N j l * ψ (i, l) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_ite_eq, mul_comm]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
theorem stateVec_swapVec_entry (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) (i : dA) (j : dB) :
    ((N ⊗ₖ (1 : Matrix dA dA ℂ)) *ᵥ swapVec ψ) (j, i) = ∑ l, N j l * ψ (i, l) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, swapVec, mul_ite,
    Finset.sum_ite_eq]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
/-- **Bob's norm is Alice's norm of the swapped state.** -/
theorem norm_stateVecB (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ N‖ = stateNorm (swapVec ψ) N := by
  classical
  rw [stateNorm, stateVecB, stateVec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm dA dB) _ _ fun p => ?_
  obtain ⟨i, j⟩ := p
  show ‖(((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ) (i, j)‖ ^ 2
      = ‖((N ⊗ₖ (1 : Matrix dA dA ℂ)) *ᵥ swapVec ψ) (j, i)‖ ^ 2
  rw [stateVecB_entry, stateVec_swapVec_entry]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] [DecidableEq dA] in
/-- The swap is a reindexing, so it preserves the norm of the state. -/
theorem swapVec_dotProduct (ψ : dA × dB → ℂ) :
    star (swapVec ψ) ⬝ᵥ swapVec ψ = star ψ ⬝ᵥ ψ :=
  (Fintype.sum_equiv (Equiv.prodComm dA dB) _ _ fun _ => rfl).symm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_nonneg (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg ψ)).1
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- Bob's version, by the swap. -/
theorem sum_stateSqNormB_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (N : POVM B dB) :
    ∑ b, ‖stateVecB ψ (((N.mats b).val))‖ ^ 2 ≤ 1 := by
  have hψ' : star (swapVec ψ) ⬝ᵥ swapVec ψ = 1 := by rw [swapVec_dotProduct]; exact hψ
  have h := sum_stateSqNorm_le_one (dA := dB) (dB := dA) (A := B) hψ' N
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) h
  rw [norm_stateVecB, stateSqNorm]
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
/-- The weighted form, over a set of questions: the shape every item of `lem:qld-win` is stated
in. -/
theorem sum_weighted_snorm_sq_triangle3 {ι κ : Type*} [Fintype κ] (v : N → ℂ)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset ι) (P Q R T : ι → κ → Matrix N N ℂ) :
    ∑ i ∈ S, w i * ∑ o, snorm v (P i o - T i o) ^ 2
      ≤ 3 * ∑ i ∈ S, w i * ∑ o, snorm v (P i o - Q i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (Q i o - R i o) ^ 2
        + 3 * ∑ i ∈ S, w i * ∑ o, snorm v (R i o - T i o) ^ 2 := by
  have hstep : ∀ i ∈ S, w i * ∑ o, snorm v (P i o - T i o) ^ 2
      ≤ 3 * (w i * ∑ o, snorm v (P i o - Q i o) ^ 2)
        + 3 * (w i * ∑ o, snorm v (Q i o - R i o) ^ 2)
        + 3 * (w i * ∑ o, snorm v (R i o - T i o) ^ 2) := by
    intro i _
    have h := sum_snorm_sq_triangle3 v (P i) (Q i) (R i) (T i)
    nlinarith [hw i]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem weightA_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) : weightA μ ψ M ≤ 1 := by
  calc weightA μ ψ M ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNorm_le_one hψ (M x)) (hμ x)
    _ = 1 := by simp [hμ1]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem weightB_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (N : X → POVM Λ dB) : weightB μ ψ N ≤ 1 := by
  calc weightB μ ψ N ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNormB_le_one hψ (N x)) (hμ x)
    _ = 1 := by simp [hμ1]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
/-- The cross deviation is at most twice the disagreement. -/
theorem xDev_le (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N ≤ 2 * (1 - agreeSum μ ψ M N) := by
  rw [xDev_eq]
  have := weightA_le_one hμ hμ1 hψ M
  have := weightB_le_one hμ hμ1 hψ N
  linarith
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
/-- **The weighted triangle inequality for cross deviations**: Alice's `A` against Bob's `D`,
through Bob's `B` and Alice's `C`. -/
theorem xDev_triangle (hμ : ∀ x, 0 ≤ μ x) (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) :
    xDev μ ψ A D ≤ 3 * xDev μ ψ A B + 3 * xDev μ ψ C B + 3 * xDev μ ψ C D := by
  have h := sum_weighted_snorm_sq_triangle3 ψ hμ (univ : Finset X)
    (fun x a => (aOp (((A x).mats a).val) : Matrix (dA × dB) (dA × dB) ℂ))
    (fun x a => bOp (((B x).mats a).val)) (fun x a => aOp (((C x).mats a).val))
    (fun x a => bOp (((D x).mats a).val))
  have hmid : ∀ x a, snorm ψ ((bOp (((B x).mats a).val) : Matrix (dA × dB) (dA × dB) ℂ)
      - aOp (((C x).mats a).val)) ^ 2
      = xSqNorm ψ (((C x).mats a).val) (((B x).mats a).val) := fun x a => by
    rw [xSqNorm_eq_snorm_sq, snorm_sub_comm]
  simp only [← xSqNorm_eq_snorm_sq, hmid] at h
  exact h
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
/-- **The agreement triangle** (`fact:triangle-for-simeq`, item 1, with `11 δ` in place of the
paper's `9 δ`): agreement is transitive across the two parties, for POVMs. -/
theorem agreeSum_triangle (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (A C : X → POVM Λ dA) (B D : X → POVM Λ dB) {δ : ℝ}
    (hAB : 1 - agreeSum μ ψ A B ≤ δ) (hCB : 1 - agreeSum μ ψ C B ≤ δ)
    (hCD : 1 - agreeSum μ ψ C D ≤ δ) :
    1 - agreeSum μ ψ A D ≤ 11 * δ := by
  have hAD := xDev_eq (μ := μ) (ψ := ψ) A D
  have htri := xDev_triangle (μ := μ) (ψ := ψ) hμ A C B D
  have h1 := xDev_le hμ hμ1 hψ A B
  have h2 := xDev_le hμ hμ1 hψ C B
  have h3 := xDev_le hμ hμ1 hψ C D
  have hwA := weightA_ge hμ hμ1 hψ A B hAB
  have hwD := weightB_ge hμ hμ1 hψ C D hCD
  linarith
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem sum_bornProb_diag_le {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA)
    (N : POVM Λ dB) : ∑ a, bornProb ψ ((M.mats a).val) ((N.mats a).val) ≤ 1 := by
  rw [← sum_bornProb hψ M N]
  exact Finset.sum_le_sum fun a _ => Finset.single_le_sum
    (f := fun b => bornProb ψ ((M.mats a).val) ((N.mats b).val))
    (fun b _ => bornProb_nonneg ψ (M.posSemidef a) (N.posSemidef b)) (Finset.mem_univ a)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
theorem dis_nonneg {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM Λ dA) (N : POVM Λ dB) :
    0 ≤ dis ψ M N :=
  sub_nonneg.mpr (sum_bornProb_diag_le hψ M N)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
variable {X : Type*} [Fintype X] [Nonempty X]
theorem one_sub_agreeSum_uniform (ψ : dA × dB → ℂ) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    1 - agreeSum (uniform X) ψ M N = (∑ x, dis ψ (M x) (N x)) / Fintype.card X := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold agreeSum dis uniform
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, sub_div, div_self hc.ne', inv_mul_eq_div]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped Kronecker
variable {Λ : Type*} [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB]
variable {X : Type*} [Fintype X] [Nonempty X]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (A C : X → POVM Λ dA)
    (B D : X → POVM Λ dB) :
    ∑ x, dis ψ (A x) (D x)
      ≤ 11 * (∑ x, dis ψ (A x) (B x) + ∑ x, dis ψ (C x) (B x) + ∑ x, dis ψ (C x) (D x)) := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hμ0 : ∀ x, 0 ≤ uniform X x := fun x => by simp [uniform]
  have hμ1 : ∑ x, uniform X x = 1 := by
    simp [uniform, Finset.card_univ]
  set δ := (∑ x, dis ψ (A x) (B x) + ∑ x, dis ψ (C x) (B x) + ∑ x, dis ψ (C x) (D x))
    / Fintype.card X
  have h1 := Finset.sum_nonneg fun x (_ : x ∈ univ) => dis_nonneg hψ (A x) (B x)
  have h2 := Finset.sum_nonneg fun x (_ : x ∈ univ) => dis_nonneg hψ (C x) (B x)
  have h3 := Finset.sum_nonneg fun x (_ : x ∈ univ) => dis_nonneg hψ (C x) (D x)
  have hAB : 1 - agreeSum (uniform X) ψ A B ≤ δ := by
    rw [one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have hCB : 1 - agreeSum (uniform X) ψ C B ≤ δ := by
    rw [one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have hCD : 1 - agreeSum (uniform X) ψ C D ≤ δ := by
    rw [one_sub_agreeSum_uniform]; exact div_le_div_of_nonneg_right (by linarith) hc.le
  have h := agreeSum_triangle hμ0 hμ1 hψ A C B D hAB hCB hCD
  rw [one_sub_agreeSum_uniform, div_le_iff₀ hc] at h
  simp only [δ] at h
  rw [mul_div_assoc', div_mul_cancel₀ _ hc.ne'] at h
  exact h
end MIPRE
