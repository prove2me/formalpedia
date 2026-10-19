-- Prove2me | solution 1 for MIPRE.OAns.sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:47:52.270397+00:00
-- url     : https://prove2.me/submissions/9557bb36-f118-43ae-b2c7-ac8a86d3292b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularGame.lean (solution of MIPRE.OAns.sum_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_OracularGame

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.OAns
open Finset
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
omit [DecidableEq A] in
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : OAns A → M) :
    ∑ u, f u = (∑ p : A × A, f (.pair p.1 p.2)) + ∑ a, f (.single a) := by
  rw [← (OAns.equivSum (A := A)).symm.sum_comp f]
  simp [Fintype.sum_sum_type, OAns.equivSum]
end MIPRE.OAns
