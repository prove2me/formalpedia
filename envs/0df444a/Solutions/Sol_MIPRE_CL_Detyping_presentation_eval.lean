-- Prove2me | solution 1 for MIPRE.CL.Detyping.presentation_eval
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:32.252059+00:00
-- url     : https://prove2.me/submissions/1c3884f3-1e06-4109-b371-400a418b356f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Detyping.lean (solution of MIPRE.CL.Detyping.presentation_eval);
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
import Theorems.Thm_MIPRE_CL_Detyping_select_output
import Theorems.Thm_MIPRE_CL_pull_proj_compl

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.supportedOn {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    P.SupportedOn T := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- A presentation on `V_T` reads only the coordinates in `T`. -/
theorem SupportedOn.eval_proj_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (hTU : T ⊆ U) (x : ι → F) : P.eval (proj U x) = P.eval x := by
  induction P generalizing T U x with
  | zero => rfl
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    have hsub : T \ S ⊆ Sᶜ := fun i hi => by
      simp only [Finset.mem_sdiff] at hi
      simpa using hi.2
    simp only [eval_cons, L₁.apply_proj_of_subset (hS.trans hTU), proj_proj]
    rw [ih _ (hnext _) (Finset.subset_inter hsub (Finset.sdiff_subset.trans hTU)) x,
      ih _ (hnext _) hsub x]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}
variable [Fintype ι]
/-- The concatenation presents `x ↦ L(x) + R_{L(x)}(x)`, when `L` is on `V_U`, the `R_u` on
`V_W`, and `U`, `W` are disjoint. -/
theorem SupportedOn.eval_concat {L : CLFun F ι k} {R : (ι → F) → CLFun F ι ℓ} {U W : Finset ι}
    (hL : L.SupportedOn U) (hR : ∀ u, (R u).SupportedOn W) (hUW : Disjoint U W) (x : ι → F) :
    (L.concat R).eval x = L.eval x + (R (L.eval x)).eval x := by
  induction L generalizing R U x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hL
    have hWS : W ⊆ Sᶜ := fun i hi =>
      Finset.mem_compl.mpr fun hiS => Finset.disjoint_left.mp hUW (hS hiS) hi
    rw [concat_cons, eval_cons, eval_cons,
      ih _ (hnext _) (fun w => hR _) (Finset.disjoint_of_subset_left Finset.sdiff_subset hUW)
        (proj Sᶜ x),
      (hR _).eval_proj_of_subset hWS, add_assoc]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
/-- Embedded factors still partition precisely the embedded original register. -/
theorem ExactlyOn.embed (e : ι ↪ κ) {P : CLFun F ι ℓ} {S : Finset ι}
    (hP : P.ExactlyOn S) : (P.embed e).ExactlyOn (S.map e) := by
  induction P generalizing S with
  | zero =>
    change S = ∅ at hP
    simp [CLFun.embed, hP]
  | cons U L next ih =>
    refine ⟨Finset.map_subset_map.mpr hP.1, fun x => ?_⟩
    rw [← Finset.map_sdiff]
    exact ih _ (hP.2 _)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι] [Fintype κ]
/-- The embedded CL function acts only on its original coordinates. -/
theorem eval_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (x : κ → F) :
    (P.embed e).eval x = push e (P.eval (pull e x)) := by
  induction P generalizing x with
  | zero => simp [embed]
  | cons S L next ih =>
    simp only [embed, eval_cons, RegLinear.embed_apply, pull_push, ih,
      pull_proj_compl, push_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Its two factors partition all four blocks on every prefix, valid or otherwise. -/
theorem presentation_exactlyOn (E : T → T → Prop) [DecidableRel E] (w : Bool) :
    (presentation E w).ExactlyOn univ := by
  simp [presentation, CLFun.ExactlyOn, Finset.compl_eq_univ_sdiff]
end
end MIPRE.CL.Graph

namespace MIPRE.CL.CLFun
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Semiring F] [DecidableEq ι]
/-- The zero fallback still partitions all registers when at least one level is available. -/
theorem zeroOn_exactlyOn (S : Finset ι) (ℓ : ℕ) (h : ℓ = 0 → S = ∅) :
    (zeroOn (F := F) S ℓ).ExactlyOn S := by
  induction ℓ generalizing S with
  | zero => exact h rfl
  | succ ℓ ih =>
    refine ⟨Subset.refl S, fun _ => ?_⟩
    simpa using ih ∅ (fun _ => rfl)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The graph and content registers are disjoint. -/
theorem disjoint_registers :
    Disjoint ((univ : Finset (Graph.Coord T)).map (Function.Embedding.inl (β := ι)))
      ((univ : Finset ι).map Function.Embedding.inr) := by
  simp [Finset.disjoint_left]
end
end MIPRE.CL.Detyping

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
theorem _root_.solution {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (x : Coord T ι → ZMod 2) :
    (presentation E w P).eval x = Sum.elim
      ((Graph.presentation E w).eval (pull .inl x))
      ((selected P (select E w (pull .inl x))).eval (pull .inr x)) := by
  have hs : ∀ u, (selected P u).ExactlyOn univ := by
    intro u
    cases u with
    | none => exact CLFun.zeroOn_exactlyOn _ _ (fun h => False.elim (by omega))
    | some t => exact hP t
  rw [presentation, CLFun.SupportedOn.eval_concat
    ((Graph.presentation_exactlyOn E w).embed .inl).supportedOn
    (fun x => ((hs _).embed .inr).supportedOn) disjoint_registers]
  simp only [CLFun.eval_embed, pull_push, select_output]
  funext j
  cases j <;> simp
end MIPRE.CL.Detyping
