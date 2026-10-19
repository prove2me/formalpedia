-- Prove2me | solution 1 for MIPRE.POVM.sum_val
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:54.685615+00:00
-- url     : https://prove2.me/submissions/8241f01b-0d15-436c-aa16-1eab99ab8deb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (solution of MIPRE.POVM.sum_val);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_POVMValue

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.POVM
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem _root_.solution {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d) :
    ∑ a, ((M.mats a).val) = (1 : Matrix d d ℂ) := by
  rw [← AddSubmonoidClass.coe_finsetSum, M.normalized]
  rfl
end MIPRE.POVM
