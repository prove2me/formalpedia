-- Prove2me | solution 1 for MIPRE.IsPVM.orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:06.209459+00:00
-- url     : https://prove2.me/submissions/434dda7a-34a2-4139-950f-d5c5ff6b5325

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (solution of MIPRE.IsPVM.orthogonal);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.IsPVM
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
omit [DecidableEq Λ] in
theorem posSemidef (h : IsPVM P) (a : Λ) : (P a).PosSemidef := by
  have : P a = (P a)ᴴ * P a := by rw [h.isSelfAdjoint, h.idem]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
end MIPRE.IsPVM

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.IsPVM
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
theorem _root_.solution (h : IsPVM P) {a b : Λ} (hab : a ≠ b) : P a * P b = 0 := by
  classical
  -- the compressions `P a P c P a` for `c ≠ a` sum to zero
  have hsum : ∑ c ∈ univ.erase a, P a * P c * P a = 0 := by
    have hall : ∑ c : Λ, P a * P c * P a = P a := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, h.sum_eq_one, Matrix.mul_one, h.idem]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hall
    have hdiag : P a * P a * P a = P a := by rw [h.idem, h.idem]
    rw [hdiag] at hall
    have := hall
    linear_combination (norm := module) this
  -- each compression is positive
  have hpos : ∀ c : Λ, (0 : Matrix n n ℂ) ≤ P a * P c * P a := by
    intro c
    have hc : P a * P c * P a = (P a)ᴴ * P c * P a := by rw [h.isSelfAdjoint]
    rw [hc]
    exact Matrix.nonneg_iff_posSemidef.mpr ((h.posSemidef c).conjTranspose_mul_mul_same _)
  have hb : P a * P b * P a = 0 := by
    refine le_antisymm ?_ (hpos b)
    calc P a * P b * P a ≤ ∑ c ∈ univ.erase a, P a * P c * P a :=
          Finset.single_le_sum (fun c _ => hpos c) (Finset.mem_erase.mpr ⟨hab.symm, mem_univ b⟩)
      _ = 0 := hsum
  -- hence `P b P a = 0`, and its adjoint
  have hstar : (P b * P a)ᴴ * (P b * P a) = 0 := by
    rw [Matrix.conjTranspose_mul, h.isSelfAdjoint, h.isSelfAdjoint]
    calc P a * P b * (P b * P a) = P a * (P b * P b) * P a := by
          simp only [Matrix.mul_assoc]
      _ = P a * P b * P a := by rw [h.idem]
      _ = 0 := hb
  have hba : P b * P a = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hstar
  have := congrArg Matrix.conjTranspose hba
  rwa [Matrix.conjTranspose_mul, h.isSelfAdjoint, h.isSelfAdjoint,
    Matrix.conjTranspose_zero] at this
end MIPRE.IsPVM
