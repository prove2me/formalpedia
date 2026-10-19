-- Prove2me | solution 1 for MIPRE.CL.Detyping.numbered_linear_graph
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:04.607978+00:00
-- url     : https://prove2.me/submissions/b32dbf86-be1a-4440-9080-f867491a97c3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgQueries.lean (solution of MIPRE.CL.Detyping.numbered_linear_graph);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Theorems.Thm_MIPRE_CL_Detyping_toBits_zero
import Theorems.Thm_MIPRE_CL_pull_proj_compl

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι] [Fintype κ]
/-- Linear-map queries from an arbitrary prefix commute with embedding. -/
theorem mapOfPrefix_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x y : κ → F) :
    (P.embed e).mapOfPrefix j x y = push e (P.mapOfPrefix j (pull e x) (pull e y)) := by
  induction P generalizing j x with
  | zero => simp [embed]
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [embed, mapOfPrefix_cons_succ, pull_proj, ih, pull_proj_compl]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- Expanding the first two levels exposes the exact prefix used for type selection. -/
theorem presentation_cons {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) :
    presentation E w P =
      .cons ((Graph.own w).map Function.Embedding.inl) ((RegLinear.id (Graph.own w)).embed .inl)
        (fun a => .cons ((Graph.own w)ᶜ.map Function.Embedding.inl)
          ((Graph.second E w (pull .inl a)).embed .inl)
          (fun b => (selected P (select E w (pull .inl (a + b)))).embed .inr)) := by
  simp [presentation, Graph.presentation, CLFun.embed, CLFun.concat]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The first linear query copies the player's own graph blocks. -/
theorem linear_first {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (x y : Coord T ι → ZMod 2) :
    (presentation E w P).mapOfPrefix 0 x y = push .inl (proj (Graph.own w) (pull .inl y)) := rfl
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The second linear query keeps the neighbor bit selected by the graph prefix. -/
theorem linear_second {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (x y : Coord T ι → ZMod 2) :
    (presentation E w P).mapOfPrefix 1 x y =
      push .inl (Graph.second E w (proj (Graph.own w) (pull .inl x)) (pull .inl y)) := by
  rw [presentation_cons]
  simp only [CLFun.mapOfPrefix_cons_succ, CLFun.mapOfPrefix_cons_zero,
    RegLinear.toLinearMap_apply, RegLinear.embed_apply, pull_proj]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem push_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    push (registerEquiv s).toEmbedding x =
      Fin.append (push graphEquiv.toEmbedding (pull .inl x)) (pull .inr x) := by
  funext i
  obtain ⟨q, rfl⟩ := (registerEquiv (T := T) s).surjective i
  calc _ = x q := push_apply (registerEquiv s).toEmbedding x q
    _ = _ := by
      cases q with
      | inl q =>
        simp only [registerEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
          Sum.map_inl, finSumFinEquiv_apply_left, Fin.append_left]
        exact (push_apply graphEquiv.toEmbedding (pull .inl x) q).symm
      | inr q => simp [registerEquiv, pull]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem toBits_append {m n : ℕ} (x : Fin m → 𝔽₂) (y : Fin n → 𝔽₂) :
    toBits (Fin.append x y) = toBits x ++ toBits y := by
  unfold toBits
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp
  · intro j; simp
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Numbering the sum registers is exactly concatenation of their bit strings. -/
theorem toBits_register (s : ℕ) (x : Coord T (Fin s) → 𝔽₂) :
    toBits (push (registerEquiv s).toEmbedding x) =
      graphBits (pull .inl x) ++ toBits (pull .inr x) := by
  rw [push_register, toBits_append]
  rfl
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem bits_split (s : ℕ) (z : Fin (graphDim T + s) → 𝔽₂) :
    toBits z =
      graphBits (pull .inl (pull (registerEquiv s).toEmbedding z)) ++
        toBits (pull .inr (pull (registerEquiv s).toEmbedding z)) := by
  rw [← toBits_register]
  congr 1
  funext i
  obtain ⟨q, rfl⟩ := (registerEquiv (T := T) s).surjective i
  exact (push_apply (registerEquiv s).toEmbedding
    (pull (registerEquiv s).toEmbedding z) q).symm
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The graph parser reads exactly the graph part of every well-formed vector. -/
theorem graphOfBits_take (s : ℕ) (z : Fin (graphDim T + s) → 𝔽₂) :
    graphOfBits ((toBits z).take (graphDim T)) =
      pull .inl (pull (registerEquiv s).toEmbedding z) := by
  rw [bits_split s z]
  simp only [← length_graphBits (pull .inl (pull (registerEquiv s).toEmbedding z)),
    List.take_left, graphOfBits_graphBits]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem graph_part_ofBits {s : ℕ} (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
    pull .inl (pull (registerEquiv s).toEmbedding (ofBits (graphDim T + s) z)) =
      graphOfBits (z.take (graphDim T)) := by
  rw [← graphOfBits_take s, toBits_ofBits hz]
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem toBits_register_graph (s : ℕ) (g : Graph.Coord T → 𝔽₂) :
    toBits (push (registerEquiv s).toEmbedding (push .inl g)) =
      graphBits g ++ List.replicate s false := by
  rw [toBits_register, pull_push]
  have h : pull (Function.Embedding.inr (α := Graph.Coord T)) (push .inl g) = (0 : Fin s → 𝔽₂) := by
    funext i; simp [pull]
  rw [h, toBits_zero]
end
end MIPRE.CL.Detyping

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem _root_.solution {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (k : ℕ) (hk : k < 2)
    (u y : Cost.BitStr) (hu : u.length = graphDim T + s) (hy : y.length = graphDim T + s) :
    toBits ((numbered E w P).mapOfPrefix k (ofBits (graphDim T + s) u) (ofBits (graphDim T + s) y)) =
      graphBits ((Graph.presentation E w.toBool).mapOfPrefix k
        (graphOfBits (u.take (graphDim T))) (graphOfBits (y.take (graphDim T)))) ++
        List.replicate s false := by
  have h : ∀ x z : Coord T (Fin s) → 𝔽₂,
      (presentation E w.toBool P).mapOfPrefix k x z =
        push .inl ((Graph.presentation E w.toBool).mapOfPrefix k (pull .inl x) (pull .inl z)) := by
    intro x z
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · exact linear_first E w.toBool P x z
    · exact linear_second E w.toBool P x z
  rw [numbered, CLFun.mapOfPrefix_embed, h, toBits_register_graph,
    graph_part_ofBits u hu, graph_part_ofBits y hy]
end MIPRE.CL.Detyping
