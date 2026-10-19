-- Prove2me | solution 1 for MIPRE.CL.Detyping.sum_valid_questions
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:44:54.860828+00:00
-- url     : https://prove2.me/submissions/5fa9514c-6490-451b-ba23-4d43108d64b8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingLaw.lean (solution of MIPRE.CL.Detyping.sum_valid_questions);
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
import Theorems.Thm_MIPRE_CL_Detyping_graph_output_of_select
import Theorems.Thm_MIPRE_CL_Detyping_presentation_eval
import Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff

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

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Encoding an ordered pair is injective. -/
theorem pairSeed_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (pairSeed E) := by
  intro uv uv' h
  apply Prod.ext
  · apply encode_injective E
    funext p
    exact congrFun h (false, p)
  · apply encode_injective E
    funext p
    exact congrFun h (true, p)
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Uniform averaging on valid seeds is uniform averaging on ordered edges, without multiplicity. -/
theorem sum_validSeeds {M : Type*} [AddCommMonoid M]
    (E : T → T → Prop) [DecidableRel E] (f : (Coord T → ZMod 2) → M) :
    ∑ z ∈ validSeeds E, f z = ∑ uv ∈ edges E, f (pairSeed E uv) := by
  exact Finset.sum_image (fun _ _ _ _ h => pairSeed_injective E h)
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- On an adjacent seed the two players select exactly its two endpoint types. -/
theorem select_pairSeed (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (w : Bool) (uv : T × T) (huv : E uv.1 uv.2) :
    select E w (Graph.pairSeed E uv) = some (if w then uv.2 else uv.1) := by
  apply (select_eq_some_iff _ _ _ _).mpr
  cases w <;> constructor
  · rfl
  · simp [Graph.pairSeed, Graph.encode, hE _ _ huv]
  · rfl
  · simp [Graph.pairSeed, Graph.encode, huv]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- On valid seeds the detyped question retains precisely the selected type's content. -/
theorem presentation_eval_valid {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (g : Graph.Coord T → ZMod 2) (v : ι → ZMod 2) {u : T}
    (hu : select E w g = some u) :
    (presentation E w P).eval (Sum.elim g v) = Sum.elim (view E w u) ((P u).eval v) := by
  rw [presentation_eval E w P hP hℓ]
  change Sum.elim ((Graph.presentation E w).eval g) ((selected P (select E w g)).eval v) = _
  rw [graph_output_of_select E w g hu, hu]
  rfl
end
end MIPRE.CL.Detyping

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
theorem _root_.solution {ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (E : T → T → Prop) [DecidableRel E] (hE : ∀ u v, E u v → E v u)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (f : (Coord T ι → ZMod 2) → (Coord T ι → ZMod 2) → M) :
    ∑ g ∈ Graph.validSeeds E, ∑ v : ι → ZMod 2,
      f ((presentation E false (P false)).eval (Sum.elim g v))
        ((presentation E true (P true)).eval (Sum.elim g v)) =
    ∑ uv ∈ Graph.edges E, ∑ v : ι → ZMod 2,
      f (Sum.elim (view E false uv.1) ((P false uv.1).eval v))
        (Sum.elim (view E true uv.2) ((P true uv.2).eval v)) := by
  rw [Graph.sum_validSeeds]
  apply Finset.sum_congr rfl
  intro uv huv
  have he : E uv.1 uv.2 := (Finset.mem_filter.mp huv).2
  apply Finset.sum_congr rfl
  intro v _
  rw [presentation_eval_valid E false (P false) (hP false) hℓ _ v
      (select_pairSeed E hE false uv he),
    presentation_eval_valid E true (P true) (hP true) hℓ _ v
      (select_pairSeed E hE true uv he)]
  rfl
end MIPRE.CL.Detyping
