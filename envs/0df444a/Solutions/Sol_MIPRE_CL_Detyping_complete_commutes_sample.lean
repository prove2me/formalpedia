-- Prove2me | solution 1 for MIPRE.CL.Detyping.complete_commutes_sample
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:22.304658+00:00
-- url     : https://prove2.me/submissions/949594bf-3200-44a3-8569-7636e4815bb3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingComplete.lean (solution of MIPRE.CL.Detyping.complete_commutes_sample);
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
import Theorems.Thm_MIPRE_CL_Detyping_decodeView_output
import Theorems.Thm_MIPRE_CL_Detyping_graph_output_of_select
import Theorems.Thm_MIPRE_CL_Detyping_presentation_eval
import Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff
import Theorems.Thm_MIPRE_CL_Graph_localValid_both_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- On samples the decoder selects the original typed content, or the trivial branch. -/
theorem decodeQuestion_output {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (g : Graph.Coord T → ZMod 2) (v : ι → ZMod 2) :
    decodeQuestion E ((presentation E w P).eval (Sum.elim g v)) =
      (select E w g).map (fun u => (w, u, (P u).eval v)) := by
  cases hs : select E w g with
  | some u =>
    rw [presentation_eval_valid E w P hP hℓ g v hs]
    exact decodeQuestion_question E w (u, (P u).eval v)
  | none =>
    rw [presentation_eval E w P hP hℓ]
    change (decodeView E ((Graph.presentation E w).eval g)).map _ = _
    rw [decodeView_output, hs]
    rfl
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- Successful selection by both players identifies the common edge seed. -/
theorem selects_pairSeed (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (g : Graph.Coord T → ZMod 2) {u v : T}
    (hu : select E false g = some u) (hv : select E true g = some v) :
    E u v ∧ g = Graph.pairSeed E (u, v) := by
  have hgu : Graph.localValid E false g := ⟨u, (select_eq_some_iff E false g u).mp hu⟩
  have hgv : Graph.localValid E true g := ⟨v, (select_eq_some_iff E true g v).mp hv⟩
  obtain ⟨uv, he, rfl⟩ := (Graph.localValid_both_iff E hE g).mp ⟨hgu, hgv⟩
  have hu' := (select_pairSeed E hE false uv he).symm.trans hu
  have hv' := (select_pairSeed E hE true uv he).symm.trans hv
  simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hu' hv'
  cases uv
  simp_all
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical Matrix Kronecker
set_option linter.unusedSectionVars false
variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]
/-- The typed distribution gives positive mass to every edge and content seed. -/
theorem typed_mu_pos {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hne : (Graph.edges E).Nonempty) (P : Bool → T → CLFun (ZMod 2) ι ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    {u v : T} (huv : E u v) (z : ι → ZMod 2) :
    0 < (typedGame E hne P D).μ (u, (P false u).eval z) (v, (P true v).eval z) := by
  let _ : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  apply (sample_dist_pos_iff _ _ _ _).mpr
  refine ⟨(⟨(u, v), by simp [Graph.edges, huv]⟩, z), ?_, ?_⟩ <;> rfl
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
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hS : S.IsPCC) (a₀ : A)
    (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2) (a b : A) :
    let R := complete E hne P D S a₀
    let x := (presentation E false (P false)).eval (Sum.elim g z)
    let y := (presentation E true (P true)).eval (Sum.elim g z)
    R.P.M (false, x) a * R.P.M (true, y) b = R.P.M (true, y) b * R.P.M (false, x) a := by
  dsimp only
  let M : Bool → A → Matrix (Fin S.d) (Fin S.d) ℂ := fun w a =>
    match decodeQuestion E ((presentation E w (P w)).eval (Sum.elim g z)) with
    | some q => S.P.M q a | none => if a = a₀ then 1 else 0
  change M false a * M true b = M true b * M false a
  dsimp only [M]
  simp only [decodeQuestion_output E false (P false) (hP false) hℓ,
    decodeQuestion_output E true (P true) (hP true) hℓ]
  cases hu : select E false g with
  | none => simp only [Option.map_none]; split_ifs <;> simp only [one_mul, mul_one, zero_mul, mul_zero]
  | some u =>
    cases hv : select E true g with
    | none => simp only [Option.map_some, Option.map_none]; split_ifs <;> simp only [one_mul, mul_one, zero_mul, mul_zero]
    | some v =>
      simp only [Option.map_some]
      apply hS
      simp only [Game.doubled_μ, and_self, ↓reduceIte]
      exact typed_mu_pos E hne P D (selects_pairSeed E hE g hu hv).1 z
end MIPRE.CL.Detyping
