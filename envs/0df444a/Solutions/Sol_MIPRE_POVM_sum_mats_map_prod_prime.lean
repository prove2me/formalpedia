-- Prove2me | solution 1 for MIPRE.POVM.sum_mats_map_prod_prime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:57.411978+00:00
-- url     : https://prove2.me/submissions/16f95bb4-4142-4fbf-ad5a-3096867735e8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (solution of MIPRE.POVM.sum_mats_map_prod_prime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.POVM
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {d : Type*} [Fintype d] [DecidableEq d]
theorem _root_.solution {ι B C : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (M : POVM ι d) (f : ι → B) (g : ι → C) (c : C) :
    ∑ b, (((M.map fun a => (f a, g a)).mats (b, c)).val) = (((M.map g).mats c).val) := by
  classical
  have hL : ∀ b : B, (((M.map fun a => (f a, g a)).mats (b, c)).val)
      = ∑ a, if (f a, g a) = (b, c) then ((M.mats a).val) else 0 := by
    intro b
    show ((∑ a ∈ univ.filter fun a => (f a, g a) = (b, c), M.mats a : selfAdjoint _)).val = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => hL b, Finset.sum_comm]
  have hR : (((M.map g).mats c).val) = ∑ a, if g a = c then ((M.mats a).val) else 0 := by
    show ((∑ a ∈ univ.filter fun a => g a = c, M.mats a : selfAdjoint _)).val = _
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_filter]
  rw [hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : g a = c
  · rw [if_pos h, Finset.sum_eq_single (f a) (fun b _ hb => if_neg fun he => hb (by
      rw [← (Prod.mk.injEq .. ▸ he : f a = b ∧ g a = c).1]))
      fun hmem => absurd (Finset.mem_univ (f a)) hmem, if_pos (by rw [h])]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun b _ => if_neg fun he => h (Prod.mk.injEq .. ▸ he).2
end MIPRE.POVM
