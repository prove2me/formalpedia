-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pivots_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:37.395979+00:00
-- url     : https://prove2.me/submissions/54b33eff-b67b-4cc4-a1dd-2d4c40e838e3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Geometry.lean (solution of MIPRE.LIDT.Adapter.pivots_span_singleton);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
theorem _root_.solution {w : Fin n → F} (hw : ∃ j, w j ≠ 0) :
    pivots (span F {w}) = {Fin.find (fun j => w j ≠ 0) hw} := by
  classical
  set p := Fin.find (fun j => w j ≠ 0) hw with hp
  have hwp : w p ≠ 0 := Fin.find_spec hw
  have hle : ∀ k ≤ (p : ℕ), (span F {w} ⊓ tail n k : Submodule F (Fin n → F)) = span F {w} := by
    intro k hk
    refine inf_eq_left.mpr ?_
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_tail]
    intro i hi
    exact not_not.mp (Fin.find_min hw (by rw [hp] at *; omega))
  have hgt : (span F {w} ⊓ tail n ((p : ℕ) + 1) : Submodule F (Fin n → F)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxs, hxt⟩ := hx
    simp only [SetLike.mem_coe] at hxs hxt
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxs
    rw [mem_tail] at hxt
    have hzero := hxt p (Nat.lt_succ_self _)
    rw [← hc] at hzero ⊢
    simp only [Pi.smul_apply, smul_eq_mul] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · simp [h]
    · exact absurd h hwp
  have hrank : finrank F (span F {w}) = 1 := finrank_span_singleton (by
    intro h
    exact hwp (by rw [h]; rfl))
  have hmem : p ∈ pivots (span F {w}) := by
    rw [mem_pivots, dimTail, dimTail, hle (p : ℕ) le_rfl, hgt, finrank_bot, hrank]
    exact Nat.zero_lt_one
  have hcard : (pivots (span F {w})).card = 1 := by rw [card_pivots, hrank]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  rw [hj] at hmem ⊢
  rw [Finset.mem_singleton] at hmem
  rw [hmem]
end MIPRE.LIDT.Adapter
