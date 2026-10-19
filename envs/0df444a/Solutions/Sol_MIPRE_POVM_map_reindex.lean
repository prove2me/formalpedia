-- Prove2me | solution 1 for MIPRE.POVM.map_reindex
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:33:37.036504+00:00
-- url     : https://prove2.me/submissions/c86ecbae-a96c-429c-b7e5-33c135d430da

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/RegisterReindex.lean (solution of MIPRE.POVM.map_reindex);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]
/-- **A POVM is determined by its operators.** The remaining fields are propositions. -/
theorem POVM.ext' {M N : POVM A d} (h : ∀ a, (((M.mats a)).val) = (((N.mats a)).val)) : M = N := by
  have hm : M.mats = N.mats := funext fun a => Subtype.ext (h a)
  obtain ⟨mM, hM1, hM2⟩ := M
  obtain ⟨mN, hN1, hN2⟩ := N
  simp only at hm
  subst hm
  rfl
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.POVM
open Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {A : Type*} [Fintype A]
variable {d d' : Type*} [Fintype d] [Fintype d'] [DecidableEq d] [DecidableEq d']
theorem _root_.solution {B : Type*} [Fintype B] [DecidableEq B] (e : d ≃ d') (f : A → B)
    (M : POVM A d) : (M.map f).reindex e = (M.reindex e).map f :=
  POVM.ext' fun b => by
    rw [POVM.reindex_mats, POVM.map_mats, POVM.map_mats]
    simp only [POVM.reindex_mats]
    exact map_sum (Matrix.reindexLinearEquiv ℂ ℂ e e) _ _
end MIPRE.POVM
