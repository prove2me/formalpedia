-- Prove2me | solution 1 for MIPRE.CL.Graph.localValid_both_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:40:33.503386+00:00
-- url     : https://prove2.me/submissions/0418fdc2-da9a-4174-9857-7ff0ab58800e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Graph.lean (solution of MIPRE.CL.Graph.localValid_both_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Graph

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Graph
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (z : Coord T → ZMod 2) :
    localValid E false z ∧ localValid E true z ↔
      ∃ uv : T × T, E uv.1 uv.2 ∧ z = pairSeed E uv := by
  constructor
  · rintro ⟨⟨u, hu, hbit⟩, ⟨v, hv, _⟩⟩
    have hbits := congrFun hv (true, u)
    have hEvu : E v u := by
      by_contra hh
      simp [encode, hh] at hbits
      simp only [Bool.not_false] at hbit
      rw [hbit] at hbits
      exact one_ne_zero hbits
    refine ⟨(u, v), hE v u hEvu, ?_⟩
    funext p
    rcases p with ⟨w, p⟩
    cases w
    · exact congrFun hu p
    · exact congrFun hv p
  · rintro ⟨⟨u, v⟩, huv, rfl⟩
    constructor
    · exact ⟨u, rfl, by simp [pairSeed, encode, hE u v huv]⟩
    · exact ⟨v, rfl, by simp [pairSeed, encode, huv]⟩
end MIPRE.CL.Graph
