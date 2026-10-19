-- Prove2me | solution 1 for MIPRE.aOp_sub
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:35.888945+00:00
-- url     : https://prove2.me/submissions/c0273af6-6a31-4cfd-92d9-ceb421d0ddcd

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OpBound.lean (solution of MIPRE.aOp_sub);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Theorems.Thm_MIPRE_aOp_add
import Theorems.Thm_MIPRE_aOp_smul

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
theorem _root_.solution (X Y : Matrix HA HA ℂ) :
    aOp (X - Y) = (aOp X : Matrix (HA × HB) _ ℂ) - aOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, aOp_add, aOp_smul]
  module
end MIPRE
