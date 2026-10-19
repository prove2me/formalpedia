-- Prove2me | solution 1 for MIPRE.CL.Detyping.complete_failAt_sample
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:25.975616+00:00
-- url     : https://prove2.me/submissions/ae17be13-9c69-4c7f-b508-2a360eac96ab

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingComplete.lean (solution of MIPRE.CL.Detyping.complete_failAt_sample);
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
import Theorems.Thm_MIPRE_CL_Detyping_complete_failAt_question
import Theorems.Thm_MIPRE_CL_Detyping_graph_output_of_select
import Theorems.Thm_MIPRE_CL_Detyping_presentation_eval
import Theorems.Thm_MIPRE_CL_Detyping_select_eq_some_iff
import Theorems.Thm_MIPRE_CL_Detyping_select_output
import Theorems.Thm_MIPRE_CL_Graph_localValid_both_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Game
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- The one computation the doubling needs, in a form independent of what kind of strategy is
being summed: the four-fold sum over the doubled alphabets collapses to the original one, the
three blocks other than `(false, ·), (true, ·)` contributing zero. -/
theorem sum_doubled (G : Game X X A A) (f : (Bool × X) → (Bool × X) → A → A → ℝ) :
    (∑ p, ∑ q, ∑ a, ∑ b,
        G.doubled.μ p q * (if G.doubled.D p q a b then 1 else 0) * f p q a b)
      = ∑ x, ∑ y, ∑ a, ∑ b,
          G.μ x y * (if G.D x y a b then 1 else 0) * f (false, x) (true, y) a b := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, doubled_μ, doubled_D]
  simp
end
end MIPRE.Game

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem value_undouble {G : Game X X A A} (S : TensorProductStrategy G.doubled.toGame) :
    S.undouble.value = S.value := by
  rw [show S.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p a ⊗ₖ S.PB.M q b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl
end
end MIPRE.TensorProductStrategy

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
/-- If a player has an invalid local sample, the detyped predicate always accepts. -/
theorem accepts_sample_of_none {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2)
    (h : select E false g = none ∨ select E true g = none) (a b : A) :
    accepts E D ((presentation E false (P false)).eval (Sum.elim g z))
      ((presentation E true (P true)).eval (Sum.elim g z)) a b = true := by
  rw [presentation_eval E false (P false) (hP false) hℓ,
    presentation_eval E true (P true) (hP true) hℓ]
  unfold accepts
  change (match select E false ((Graph.presentation E false).eval g),
    select E true ((Graph.presentation E true).eval g) with
    | some u, some v => _ | _, _ => true) = _
  rw [select_output, select_output]
  rcases h with h | h
  · rw [h]
  · rw [h]; cases select E false g <;> rfl
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
    (S : SyncStrategy (typedGame E hne P D).doubled) (hval : S.value = 1) (a₀ : A)
    (g : Graph.Coord T → ZMod 2) (z : ι → ZMod 2) :
    (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
      ((presentation E false (P false)).eval (Sum.elim g z))
      ((presentation E true (P true)).eval (Sum.elim g z)) = 0 := by
  by_cases h : select E false g = none ∨ select E true g = none
  · exact failAt_zero_of_accepts _ _ _ (accepts_sample_of_none E P hP hℓ D g z h)
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (fun hu => h (Or.inl hu))
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (fun hv => h (Or.inr hv))
    have he : E u v := (selects_pairSeed E hE g hu hv).1
    rw [presentation_eval_valid E false (P false) (hP false) hℓ g z hu,
      presentation_eval_valid E true (P true) (hP true) hℓ g z hv]
    change (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
      (question E false (u, (P false u).eval z)) (question E true (v, (P true v).eval z)) = 0
    rw [complete_failAt_question E hne P D S a₀ _ _ he]
    let _ : Nonempty (Edge E) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    have hs : S.toTensorProductStrategy.undouble.value = 1 := by
      rw [TensorProductStrategy.value_undouble, SyncStrategy.value_toTensorProductStrategy, hval]
    exact sample_failAt_zero (typedQuestion (E := E) P false) (typedQuestion P true) D
      S.toTensorProductStrategy.undouble hs (⟨(u, v), by simp [Graph.edges, he]⟩, z)
end MIPRE.CL.Detyping
