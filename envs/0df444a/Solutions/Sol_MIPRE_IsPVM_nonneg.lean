-- Prove2me | solution 1 for MIPRE.IsPVM.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:00.883962+00:00
-- url     : https://prove2.me/submissions/99437948-fa47-4040-9cca-7e5280566f41

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (solution of MIPRE.IsPVM.nonneg);
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
omit [DecidableEq Λ] in
theorem _root_.solution (h : IsPVM P) (a : Λ) : (0 : Matrix n n ℂ) ≤ P a :=
  Matrix.nonneg_iff_posSemidef.mpr (h.posSemidef a)
end MIPRE.IsPVM
