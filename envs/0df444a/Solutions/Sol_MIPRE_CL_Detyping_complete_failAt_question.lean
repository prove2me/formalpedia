-- Prove2me | solution 1 for MIPRE.CL.Detyping.complete_failAt_question
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:16.999853+00:00
-- url     : https://prove2.me/submissions/d7336f00-74cf-48c3-bcbd-a2c18417dba8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingComplete.lean (solution of MIPRE.CL.Detyping.complete_failAt_question);
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingComplete
import Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
variable {T ι A B : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [Fintype B]
/-- On an edge, the fixed graph views make the detyped predicate exactly the typed one. -/
theorem accepts_question (E : T → T → Prop) [DecidableRel E]
    (D : Question T ι → Question T ι → A → B → Bool)
    (x y : Question T ι) (h : E x.1 y.1) (a : A) (b : B) :
    accepts E D (question E false x) (question E true y) a b = D x y a b := by
  unfold accepts question
  change (match select E false (view E false x.1), select E true (view E true y.1) with
    | some u, some v =>
      if E u v ∧ view E false x.1 = view E false u ∧ view E true y.1 = view E true v then
        D (u, x.2) (v, y.2) a b else true
    | _, _ => true) = _
  rw [select_view, select_view]
  simp [h]
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
/-- A fixed embedded typed question is decoded exactly. -/
theorem decodeQuestion_question (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (q : Question T ι) : decodeQuestion E (question E w q) = some (w, q) := by
  change (decodeView E (view E w q.1)).map _ = _
  rw [decodeView_view]
  rfl
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical Matrix Kronecker
set_option linter.unusedSectionVars false
variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]
/-- On every valid view the common measurement rule is the original typed rule. -/
theorem complete_M_question {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A)
    (tag w : Bool) (q : Question T ι) (a : A) :
    (complete E hne P D S a₀).P.M (tag, question E w q) a = S.P.M (w, q) a := by
  change (match decodeQuestion E (question E w q) with
    | some q' => S.P.M q' a | none => if a = a₀ then 1 else 0) = _
  rw [decodeQuestion_question]
end
end MIPRE.CL.Detyping

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical Matrix Kronecker
set_option linter.unusedSectionVars false
variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]
theorem _root_.solution {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (a₀ : A)
    (x y : Question T ι) (hxy : E x.1 y.1) :
    (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
      (question E false x) (question E true y) =
      S.toTensorProductStrategy.undouble.failAt x y := by
  unfold TensorProductStrategy.failAt TensorProductStrategy.succAt
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (if accepts E D (question E false x) (question E true y) a b then 1 else 0) *
      (star (maxEntangled S.d) ⬝ᵥ
        (((complete E hne P D S a₀).P.M (false, question E false x) a ⊗ₖ
          ((complete E hne P D S a₀).P.M (true, question E true y) b)ᵀ) *ᵥ maxEntangled S.d)).re = _
  rw [accepts_question E D x y hxy, complete_M_question, complete_M_question]
  rfl
end MIPRE.CL.Detyping
