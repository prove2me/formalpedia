-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pivots_line
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:35.971212+00:00
-- url     : https://prove2.me/submissions/4c0995ea-b2c1-4eb2-a71c-7de75b4871b8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Geometry.lean (solution of MIPRE.LIDT.Adapter.pivots_line);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- The coordinate line `span {eᵢ}` meets `tail n k` in itself when `k ≤ i`: a multiple of
`eᵢ` has all its other coordinates zero already. -/
theorem inf_tail_of_le (i : Fin n) (k : ℕ) (hk : k ≤ (i : ℕ)) :
    (span F {(Pi.single i 1 : Fin n → F)} ⊓ tail n k : Submodule F (Fin n → F))
      = span F {(Pi.single i 1 : Fin n → F)} := by
  refine inf_eq_left.mpr ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_tail]
  intro j hj
  rw [Pi.single_apply, if_neg (fun h : j = i => by subst h; omega)]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- And meets it in `⊥` when `k > i`: the `i`-th coordinate is then forced to vanish. -/
theorem inf_tail_of_gt (i : Fin n) (k : ℕ) (hk : (i : ℕ) < k) :
    (span F {(Pi.single i 1 : Fin n → F)} ⊓ tail n k : Submodule F (Fin n → F)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxs, hxt⟩ := hx
  simp only [SetLike.mem_coe] at hxs hxt
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxs
  rw [mem_tail] at hxt
  have hi := hxt i hk
  rw [← hc] at hi ⊢
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hi
  simp [hi]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
theorem single_ne_zero (i : Fin n) : (Pi.single i 1 : Fin n → F) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
theorem finrank_line (i : Fin n) :
    finrank F (span F {(Pi.single i 1 : Fin n → F)}) = 1 :=
  finrank_span_singleton (single_ne_zero i)
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
theorem _root_.solution (i : Fin n) :
    pivots (span F {(Pi.single i 1 : Fin n → F)}) = {i} := by
  classical
  set S := span F {(Pi.single i 1 : Fin n → F)} with hS
  have hmem : i ∈ pivots S := by
    rw [mem_pivots, dimTail, dimTail, hS, inf_tail_of_le i (i : ℕ) le_rfl,
      inf_tail_of_gt i ((i : ℕ) + 1) (Nat.lt_succ_self _)]
    rw [finrank_bot, ← hS, finrank_line]
    exact Nat.zero_lt_one
  have hcard : (pivots S).card = 1 := by rw [card_pivots, hS, finrank_line]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  rw [hj] at hmem ⊢
  rw [Finset.mem_singleton] at hmem
  rw [hmem]
end MIPRE.LIDT.Adapter
