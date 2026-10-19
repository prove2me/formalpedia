-- Prove2me | solution 1 for MIPRE.CL.Graph.decode_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:40:03.481968+00:00
-- url     : https://prove2.me/submissions/510774c5-8168-41ca-8ead-333c48c3d6f9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Graph.lean (solution of MIPRE.CL.Graph.decode_eq_some_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Graph

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
namespace MIPRE.CL.Graph
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E]
    (x : Bool × T → ZMod 2) (u : T) : decode E x = some u ↔ x = encode E u := by
  unfold decode
  split_ifs with h
  · constructor
    · intro he
      have hc := Option.some.inj he
      exact h.choose_spec.trans (congrArg (encode E) hc)
    · intro hx
      congr 1
      exact encode_injective E (h.choose_spec.symm.trans hx)
  · constructor
    · intro he
      cases he
    · intro hx
      exact False.elim (h ⟨u, hx⟩)
end MIPRE.CL.Graph
