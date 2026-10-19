-- Prove2me | solution 1 for MIPRE.kronecker_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:02.197505+00:00
-- url     : https://prove2.me/submissions/618e73fe-93b9-452b-9501-db2122db83ad

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (solution of MIPRE.kronecker_sum_right);
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
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem _root_.solution {dA dB ι : Type*} (M : Matrix dA dA ℂ) (s : Finset ι)
    (f : ι → Matrix dB dB ℂ) : M ⊗ₖ (∑ i ∈ s, f i) = ∑ i ∈ s, M ⊗ₖ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.kronecker_add, ih, Finset.sum_insert hi]
end MIPRE
