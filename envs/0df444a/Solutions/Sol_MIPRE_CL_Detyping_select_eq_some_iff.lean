-- Prove2me | solution 1 for MIPRE.CL.Detyping.select_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:40:32.773531+00:00
-- url     : https://prove2.me/submissions/ce0cca34-e59d-4130-828c-7152b1a70abd

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Detyping.lean (solution of MIPRE.CL.Detyping.select_eq_some_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Theorems.Thm_MIPRE_CL_Graph_decode_eq_some_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The one-hot half makes the encoding injective, even for an isolated vertex. -/
theorem encode_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (encode E) := by
  intro u v h
  have hh := congrFun h (false, u)
  by_contra huv
  simpa [encode, huv] using hh
end
end MIPRE.CL.Graph

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) (u : T) :
    select E w g = some u ↔
      (fun p => g (w, p)) = Graph.encode E u ∧ g (!w, (true, u)) = 1 := by
  unfold select
  cases hd : Graph.decode E (fun p => g (w, p)) with
  | none =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hu
    have := (Graph.decode_eq_some_iff E _ u).mpr hu
    rw [hd] at this
    cases this
  | some v =>
    have hv := (Graph.decode_eq_some_iff E _ v).mp hd
    by_cases hb : g (!w, (true, v)) = 1
    · simp only [if_pos hb, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨hv, hb⟩
      · intro hu
        exact Graph.encode_injective E (hv.symm.trans hu.1)
    · simp only [if_neg hb, reduceCtorEq, false_iff, not_and]
      intro hu hbit
      have h := Graph.encode_injective E (hv.symm.trans hu)
      subst v
      exact hb hbit
end MIPRE.CL.Detyping
