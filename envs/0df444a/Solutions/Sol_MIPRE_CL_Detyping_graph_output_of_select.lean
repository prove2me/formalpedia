-- Prove2me | solution 1 for MIPRE.CL.Detyping.graph_output_of_select
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:10.977847+00:00
-- url     : https://prove2.me/submissions/393a8741-c460-4217-ab63-d732c2f7962d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingLaw.lean (solution of MIPRE.CL.Detyping.graph_output_of_select);
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff
import Theorems.Thm_MIPRE_CL_Graph_decode_eq_some_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Projecting onto one's own first-stage block does not affect decoding. -/
theorem mask_proj_own (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) : mask E w (proj (own w) z) = mask E w z := by
  unfold mask
  have he : (fun p => proj (own w) z (w, p)) = fun p => z (w, p) := by
    funext p
    simp
  rw [he]
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The semantic output is the own block plus the selected opposite neighbor bit. -/
theorem presentation_eval (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (z : Coord T → ZMod 2) :
    (presentation E w).eval z = proj (own w) z + proj (mask E w z) z := by
  simp only [presentation, CLFun.eval_cons, CLFun.eval_zero, add_zero, RegLinear.id_apply]
  change _ + proj (mask E w (proj (own w) z)) (proj (own w)ᶜ z) = _
  rw [mask_proj_own, proj_proj_of_subset (mask_subset E w z)]
end
end MIPRE.CL.Graph

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) {u : T} (h : select E w g = some u) :
    (Graph.presentation E w).eval g = view E w u := by
  obtain ⟨hu, hbit⟩ := (select_eq_some_iff E w g u).mp h
  have hd := (Graph.decode_eq_some_iff E _ u).mpr hu
  rw [Graph.presentation_eval]
  unfold Graph.mask
  rw [hd]
  funext ⟨b, q⟩
  by_cases hb : b = w
  · subst b
    simpa [view] using congrFun hu q
  · simp only [Pi.add_apply, proj_apply, Graph.mem_own, hb, if_false,
      Finset.mem_singleton, zero_add, view]
    split_ifs with he
    · rw [he]
      exact hbit
    · rfl
end MIPRE.CL.Detyping
