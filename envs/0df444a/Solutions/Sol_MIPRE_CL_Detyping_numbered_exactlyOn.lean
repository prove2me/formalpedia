-- Prove2me | solution 1 for MIPRE.CL.Detyping.numbered_exactlyOn
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:05.555653+00:00
-- url     : https://prove2.me/submissions/be794048-9082-4712-ac75-d6a78821cfcb

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgBits.lean (solution of MIPRE.CL.Detyping.numbered_exactlyOn);
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
import Theorems.Thm_MIPRE_CL_CLFun_ExactlyOn_concat

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The graph and content registers exhaust the ambient space. -/
theorem union_registers :
    ((univ : Finset (Graph.Coord T)).map (Function.Embedding.inl (β := ι))) ∪
      ((univ : Finset ι).map Function.Embedding.inr) = univ := by
  ext x
  cases x <;> simp
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
/-- The full detyped sampler partitions its registers on every branch, including rejection. -/
theorem presentation_exactlyOn {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Bool)
    (P : T → CLFun (ZMod 2) ι ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ) :
    (presentation E w P).ExactlyOn univ := by
  have hs : ∀ u, (selected P u).ExactlyOn univ := by
    intro u
    cases u with
    | none => exact CLFun.zeroOn_exactlyOn _ _ (fun h => False.elim (by omega))
    | some t => exact hP t
  rw [presentation, ← union_registers (T := T) (ι := ι)]
  exact ((Graph.presentation_exactlyOn E w).embed .inl).concat
    (fun x => (hs _).embed .inr) disjoint_registers
end
end MIPRE.CL.Detyping

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem _root_.solution {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ) :
    (numbered E w P).ExactlyOn univ := by
  have h := (presentation_exactlyOn E w.toBool P hP hℓ).embed (registerEquiv s).toEmbedding
  simpa [numbered] using h
end MIPRE.CL.Detyping
