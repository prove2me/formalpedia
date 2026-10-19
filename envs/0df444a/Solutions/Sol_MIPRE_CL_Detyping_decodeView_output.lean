-- Prove2me | solution 1 for MIPRE.CL.Detyping.decodeView_output
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:21.955516+00:00
-- url     : https://prove2.me/submissions/5be11952-9ade-4a23-82de-b744e0d5e652

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingCompleteSupport.lean (solution of MIPRE.CL.Detyping.decodeView_output);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
import Theorems.Thm_MIPRE_CL_Detyping_graph_output_of_select
import Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff
import Theorems.Thm_MIPRE_CL_Detyping_select_output

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

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- A valid graph view decodes to its type. -/
theorem select_view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) :
    select E w (view E w u) = some u := by
  apply (select_eq_some_iff _ _ _ _).mpr
  constructor
  · funext p
    simp [view]
  · simp [view]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- The two players' families of valid graph views are disjoint. -/
theorem view_disjoint (E : T → T → Prop) [DecidableRel E] (u v : T) :
    view E false u ≠ view E true v := by
  intro h
  have hh := congrFun h (false, (false, u))
  simp [view, Graph.encode] at hh
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- Graph views uniquely determine the type within either pattern family. -/
theorem view_injective (E : T → T → Prop) [DecidableRel E] (w : Bool) :
    Function.Injective (view E w) := by
  intro u v h
  have hs := congrArg (select E w) h
  simpa only [select_view, Option.some.injEq] using hs
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The common decoder recognizes every valid question with its original tag. -/
theorem decodeView_view (E : T → T → Prop) [DecidableRel E] (w : Bool) (u : T) :
    decodeView E (view E w u) = some (w, u) := by
  cases w
  · have h : ∃ v, view E false u = view E false v := ⟨u, rfl⟩
    simp only [decodeView, dif_pos h]
    rw [← view_injective E false h.choose_spec]
  · have h : ¬∃ v, view E true u = view E false v := by
      rintro ⟨v, hv⟩
      exact view_disjoint E v u hv.symm
    have h' : ∃ v, view E true u = view E true v := ⟨u, rfl⟩
    simp only [decodeView, dif_neg h, dif_pos h']
    rw [← view_injective E true h'.choose_spec]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The graph sampler always erases the other player's vertex block. -/
theorem graph_output_opposite_vertex (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) (u : T) :
    (Graph.presentation E w).eval g (!w, (false, u)) = 0 := by
  rw [Graph.presentation_eval]
  simp only [Pi.add_apply, proj_apply, Graph.mem_own, Bool.not_eq_self, if_false, zero_add]
  unfold Graph.mask
  cases Graph.decode E (fun p => g (w, p)) <;> simp
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- A sampled graph view cannot be a valid view of the opposite player. -/
theorem graph_output_ne_opposite_view (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) (u : T) :
    (Graph.presentation E w).eval g ≠ view E (!w) u := by
  intro h
  have hh := congrFun h (!w, (false, u))
  rw [graph_output_opposite_vertex] at hh
  simp [view, Graph.encode] at hh
end
end MIPRE.CL.Detyping

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (g : Graph.Coord T → ZMod 2) :
    decodeView E ((Graph.presentation E w).eval g) = (select E w g).map (w, ·) := by
  cases hs : select E w g with
  | some u => rw [graph_output_of_select E w g hs, decodeView_view]; rfl
  | none =>
    have hown : ¬∃ u, (Graph.presentation E w).eval g = view E w u := by
      rintro ⟨u, hu⟩
      have hh := congrArg (select E w) hu
      rw [select_output, select_view, hs] at hh
      cases hh
    have hopp : ¬∃ u, (Graph.presentation E w).eval g = view E (!w) u := by
      rintro ⟨u, hu⟩
      exact graph_output_ne_opposite_view E w g u hu
    cases w <;> simp only [Bool.not_false, Bool.not_true] at hopp <;>
      simp [decodeView, hown, hopp]
end MIPRE.CL.Detyping
