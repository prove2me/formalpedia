-- Prove2me | solution 1 for MIPRE.Introspection.commutator_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:31.356734+00:00
-- url     : https://prove2.me/submissions/f750abf5-08b8-4c7d-b92b-4c8c8c4e3840

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwoSidedCommutation.lean (solution of MIPRE.Introspection.commutator_product_bound);
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
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le

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
/-- **A rectangular isometry preserves the norm.** -/
theorem norm_evec_mulVec_eq {M : Type*} [Fintype M] {A : Matrix M N ℂ} [DecidableEq N]
    (h : Aᴴ * A = 1) (v : N → ℂ) : ‖evec (A *ᵥ v)‖ = ‖evec v‖ := by
  have hsq : ‖evec (A *ᵥ v)‖ ^ 2 = ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, h, Matrix.one_mulVec, norm_evec_sq]
  nlinarith [norm_nonneg (evec (A *ᵥ v)), norm_nonneg (evec v), hsq]
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
/-- An isometry in front changes nothing. -/
theorem snorm_mul_of_isometry [DecidableEq N] {M : Matrix N N ℂ} (h : Mᴴ * M = 1)
    (M' : Matrix N N ℂ) :
    snorm v (M * M') = snorm v M' := by
  rw [snorm, snorm, ← Matrix.mulVec_mulVec, norm_evec_mulVec_eq h]
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A]
theorem _root_.solution (ψ : N → ℂ) (M : A → Matrix N N ℂ)
    (hM : ∑ a, (M a)ᴴ * M a ≤ (1 : Matrix N N ℂ))
    (U V W : Matrix N N ℂ) (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1)
    (hWU : W * U = U * W) (hWM : ∀ a, W * M a = M a * W) :
    (∑ a, snorm ψ (M a * (U * V) - (U * V) * M a) ^ 2) ≤
      4 * (∑ a, snorm ψ (M a * U - U * M a) ^ 2) +
      4 * (∑ a, snorm ψ (M a * V - V * M a) ^ 2) +
      8 * snorm ψ (V - W) ^ 2 := by
  let P₀ a := M a * U * V
  let P₁ a := M a * U * W
  let P₂ a := U * M a * W
  let P₃ a := U * M a * V
  let P₄ a := U * V * M a
  have h01 : (∑ a, snorm ψ (P₀ a - P₁ a) ^ 2) ≤ snorm ψ (V - W) ^ 2 := by
    have h := sum_snorm_sq_mul_le ψ M hM (U * (V - W))
    simp only [snorm_mul_of_isometry ψ hU] at h
    convert h using 1
    congr 1
    funext a
    congr 2
    dsimp [P₀, P₁]
    noncomm_ring
  have h12 : (∑ a, snorm ψ (P₁ a - P₂ a) ^ 2) =
      ∑ a, snorm ψ (M a * U - U * M a) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    have he : P₁ a - P₂ a = W * (M a * U - U * M a) := by
      dsimp [P₁, P₂]
      have h₁ : W * (M a * U) = M a * U * W := by
        rw [← mul_assoc, hWM, mul_assoc, hWU, ← mul_assoc]
      have h₂ : W * (U * M a) = U * M a * W := by
        rw [← mul_assoc, hWU, mul_assoc, hWM, ← mul_assoc]
      rw [mul_sub, h₁, h₂]
    rw [he, snorm_mul_of_isometry ψ hW]
  have h23 : (∑ a, snorm ψ (P₂ a - P₃ a) ^ 2) ≤ snorm ψ (V - W) ^ 2 := by
    have he a : P₂ a - P₃ a = U * (M a * (W - V)) := by
      dsimp [P₂, P₃]
      noncomm_ring
    simp_rw [he, snorm_mul_of_isometry ψ hU]
    exact (sum_snorm_sq_mul_le ψ M hM (W - V)).trans_eq
      (congrArg (fun x : ℝ => x ^ 2) (snorm_sub_comm ψ W V))
  have h34 : (∑ a, snorm ψ (P₃ a - P₄ a) ^ 2) =
      ∑ a, snorm ψ (M a * V - V * M a) ^ 2 := by
    have he a : P₃ a - P₄ a = U * (M a * V - V * M a) := by
      dsimp [P₃, P₄]
      noncomm_ring
    simp_rw [he, snorm_mul_of_isometry ψ hU]
  have h04 := sum_snorm_sq_triangle' ψ P₀ P₂ P₄
  have h02 := sum_snorm_sq_triangle' ψ P₀ P₁ P₂
  have h24 := sum_snorm_sq_triangle' ψ P₂ P₃ P₄
  have hend : (∑ a, snorm ψ (M a * (U * V) - (U * V) * M a) ^ 2) =
      ∑ a, snorm ψ (P₀ a - P₄ a) ^ 2 := by simp only [P₀, P₄, mul_assoc]
  rw [hend]
  linarith
end MIPRE.Introspection
