-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.card_filter_diag_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:46.615674+00:00
-- url     : https://prove2.me/submissions/171672f7-d144-4757-b0ff-42579240bcb6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.card_filter_diag_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights
import Theorems.Thm_MIPRE_LIDT_Adapter_of_questions_diag

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- `Sample.extend` is the extension by zero, so it recovers `v` on `v`'s own indices. -/
theorem extend_apply_coe {j : Fin m} (v : Fin ((j : ℕ) + 1) → F) (i : Fin ((j : ℕ) + 1)) :
    (Sample.extend v : Point F m)
        ⟨(i : ℕ), lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.isLt⟩ = v i := by
  rw [Sample.extend, dif_pos (Nat.le_of_lt_succ i.isLt)]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) (u : Point F m) :
    (Finset.univ.filter (fun s : Sample F m =>
        s.questions = ((Question.diagLine ℓ : Question F m), Question.point u))).card
      ≤ m * Fintype.card F := by
  classical
  set p := Fin.find (fun k => ℓ.2 k ≠ 0) hℓ with hp
  have hlp : ℓ.2 p ≠ 0 := Fin.find_spec hℓ
  have hcard : (Finset.univ : Finset (Fin m × F)).card = m * Fintype.card F := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (diagKey p) (fun _ _ => Finset.mem_univ _) ?_
  intro s₁ h₁ s₂ h₂ hkey
  obtain ⟨j₁, v₁, hs₁, c₁, hc₁, hcv₁⟩ :=
    of_questions_diag hℓ (Finset.mem_filter.mp h₁).2
  obtain ⟨j₂, v₂, hs₂, c₂, hc₂, hcv₂⟩ :=
    of_questions_diag hℓ (Finset.mem_filter.mp h₂).2
  subst hs₁
  subst hs₂
  obtain ⟨hj, hval⟩ := (Prod.mk.injEq _ _ _ _).mp hkey
  -- the scalars agree
  have hc : c₁ = c₂ := by
    have e₁ : (Sample.extend v₁ : Point F m) p = c₁ * ℓ.2 p := by
      rw [hcv₁]; simp
    have e₂ : (Sample.extend v₂ : Point F m) p = c₂ * ℓ.2 p := by
      rw [hcv₂]; simp
    rw [e₁, e₂] at hval
    exact mul_right_cancel₀ hlp hval
  subst hj
  subst hc
  -- hence the directions, hence `v`
  have hext : (Sample.extend v₁ : Point F m) = Sample.extend v₂ := by rw [hcv₁, hcv₂]
  have hv : v₁ = v₂ := by
    funext i
    rw [← extend_apply_coe v₁ i, ← extend_apply_coe v₂ i, hext]
  rw [hv]
end MIPRE.LIDT.Adapter
