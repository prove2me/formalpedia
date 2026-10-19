-- Prove2me | solution 1 for MIPRE.POVM.ext_prime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:38.342308+00:00
-- url     : https://prove2.me/submissions/d3f5bb07-2c31-4016-b14b-66e6a5f0192a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Distances.lean (solution of MIPRE.POVM.ext_prime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.POVM
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]
theorem _root_.solution {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N := by
  have hm : M.mats = N.mats := funext fun a => Subtype.ext (h a)
  obtain ⟨mM, hM1, hM2⟩ := M
  obtain ⟨mN, hN1, hN2⟩ := N
  simp only at hm
  subst hm
  rfl
end MIPRE.POVM
