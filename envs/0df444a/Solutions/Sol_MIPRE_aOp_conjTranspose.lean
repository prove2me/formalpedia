-- Prove2me | solution 1 for MIPRE.aOp_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:50.708694+00:00
-- url     : https://prove2.me/submissions/bb8c2d56-c088-4364-86f7-952b2e90d82a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OpBound.lean (solution of MIPRE.aOp_conjTranspose);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem _root_.solution (X : Matrix HA HA ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ)ᴴ = aOp (Xᴴ) := by
  rw [aOp, aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
end MIPRE
