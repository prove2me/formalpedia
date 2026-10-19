-- Prove2me | solution 1 for MIPRE.LCS.binary_measurement_eq_projector
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:39:39.205295+00:00
-- url     : https://prove2.me/submissions/5c2dd9b1-b5a2-417e-8dbe-c765979db617

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Observable.lean (solution of MIPRE.LCS.binary_measurement_eq_projector);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LCS
section
/-- The `ZMod 2` counterpart of `Fin.sum_univ_two`. -/
lemma sum_univ_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ x, f x = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
end
end MIPRE.LCS

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LCS
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
theorem _root_.solution (f : ZMod 2 → R) (h : IsMeasurementSystem f) (y : ZMod 2) :
    f y = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • observableOfMeasurementSystem f) := by
  have hsum := h.sum_one
  rw [sum_univ_zmod_two] at hsum
  unfold observableOfMeasurementSystem
  have hy : y = 0 ∨ y = 1 := zmod_two_eq_zero_or_one y
  rcases hy with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, one_smul, ← hsum]
    have h1 : f 0 + f 1 + (f 0 - f 1) = f 0 + f 0 := by abel
    rw [h1, ← one_smul ℂ (f 0), ← add_smul]
    have h2 : (1 / 2 : ℂ) * (1 + 1 : ℂ) = 1 := by norm_num
    rw [smul_smul, h2, one_smul]
  · simp only [zmod_two_val_one, pow_one]
    have h1 : (1 : R) + (-1 : ℂ) • (f 0 - f 1) = f 1 + f 1 := by
      rw [← hsum, neg_smul, one_smul]; abel
    rw [h1, ← one_smul ℂ (f 1), ← add_smul]
    have h2 : (1 / 2 : ℂ) * (1 + 1 : ℂ) = 1 := by norm_num
    rw [smul_smul, h2, one_smul]
end MIPRE.LCS
