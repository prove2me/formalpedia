-- Prove2me | solution 1 for MIPRE.IsPVM.posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:30:05.894627+00:00
-- url     : https://prove2.me/submissions/4d00b184-9350-4e17-8e9d-29526e1af82f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (solution of MIPRE.IsPVM.posSemidef);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.IsPVM
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
omit [DecidableEq Λ] in
theorem _root_.solution (h : IsPVM P) (a : Λ) : (P a).PosSemidef := by
  have : P a = (P a)ᴴ * P a := by rw [h.isSelfAdjoint, h.idem]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end MIPRE.IsPVM
