-- Prove2me | solution 1 for MIPRE.bnd_one_of_conjTranspose_mul_self_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:18.9121+00:00
-- url     : https://prove2.me/submissions/bc13c90b-de64-4a9e-8567-eed15288e567

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OpBound.lean (solution of MIPRE.bnd_one_of_conjTranspose_mul_self_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
theorem _root_.solution {M : Matrix N N ℂ}
    (h : (Mᴴ * M) ≤ (1 : Matrix N N ℂ)) : Bnd M 1 := by
  intro v
  have hsq : ‖evec (M *ᵥ v)‖ ^ 2 ≤ ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, norm_evec_sq]
    have hpsd : (0 : Matrix N N ℂ) ≤ 1 - Mᴴ * M := sub_nonneg.mpr h
    have hnn : (0 : ℂ) ≤ star v ⬝ᵥ (((1 : Matrix N N ℂ) - Mᴴ * M) *ᵥ v) :=
      (Matrix.nonneg_iff_posSemidef.mp hpsd).dotProduct_mulVec_nonneg v
    have hsplit : star v ⬝ᵥ (((1 : Matrix N N ℂ) - Mᴴ * M) *ᵥ v)
        = (star v ⬝ᵥ v) - star v ⬝ᵥ ((Mᴴ * M) *ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
    rw [hsplit] at hnn
    have := (Complex.nonneg_iff.mp hnn).1
    simp only [Complex.sub_re] at this
    linarith
  rw [one_mul]
  nlinarith [norm_nonneg (evec (M *ᵥ v)), norm_nonneg (evec v), hsq]
end MIPRE
