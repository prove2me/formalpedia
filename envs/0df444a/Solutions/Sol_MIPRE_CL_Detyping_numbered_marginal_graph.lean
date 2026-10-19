-- Prove2me | solution 1 for MIPRE.CL.Detyping.numbered_marginal_graph
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:08.391985+00:00
-- url     : https://prove2.me/submissions/55ca7452-4a73-46b9-8db1-165a722d1b49

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgQueries.lean (solution of MIPRE.CL.Detyping.numbered_marginal_graph);
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
import Theorems.Thm_MIPRE_CL_CLFun_truncate_concat_le
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
/-- Marginal queries are transported by the same coordinate embedding. -/
theorem eval_truncate_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x : κ → F) :
    ((P.embed e).truncate j).eval x = push e ((P.truncate j).eval (pull e x)) := by
  induction j generalizing ℓ P x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => simp [embed, eval_truncate_zero]
    | cons S L next =>
      simp only [embed, truncate_succ_cons, eval_cons, RegLinear.embed_apply,
        pull_push, ih, pull_proj_compl, push_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- Marginals through level two are precisely graph marginals with zero content. -/
theorem marginal_graph {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (j : ℕ) (hj : j ≤ 2) (x : Coord T ι → ZMod 2) :
    ((presentation E w P).truncate j).eval x =
      push .inl (((Graph.presentation E w).truncate j).eval (pull .inl x)) := by
  rw [presentation, CLFun.truncate_concat_le _ _ j hj, CLFun.eval_truncate_embed]
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
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (j : ℕ) (hj : j ≤ 2)
    (z : Cost.BitStr) (hz : z.length = graphDim T + s) :
    toBits (((numbered E w P).truncate j).eval (ofBits (graphDim T + s) z)) =
      graphBits (((Graph.presentation E w.toBool).truncate j).eval
        (graphOfBits (z.take (graphDim T)))) ++ List.replicate s false := by
  rw [numbered, CLFun.eval_truncate_embed, marginal_graph E w.toBool P j hj,
    toBits_register_graph, graph_part_ofBits z hz]
end MIPRE.CL.Detyping
