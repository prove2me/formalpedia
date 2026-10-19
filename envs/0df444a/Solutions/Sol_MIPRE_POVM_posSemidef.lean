-- Prove2me | solution 1 for MIPRE.POVM.posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:55.430637+00:00
-- url     : https://prove2.me/submissions/2ffeb31a-3190-4afe-8afd-bdf4decf8fe9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (solution of MIPRE.POVM.posSemidef);
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
theorem _root_.solution {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (a : A) : ((M.mats a).val).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr (M.nonneg a))
end MIPRE.POVM
