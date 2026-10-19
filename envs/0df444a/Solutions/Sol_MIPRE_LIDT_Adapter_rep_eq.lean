-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.rep_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:29:32.401648+00:00
-- url     : https://prove2.me/submissions/750002fb-58a6-4fdd-9da9-d66ff774601a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Geometry.lean (solution of MIPRE.LIDT.Adapter.rep_eq);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_pivots_span_singleton

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- Uniqueness of the decomposition along complementary submodules, as a rewriting rule:
an element of `p` congruent to `x` modulo `q` *is* the projection of `x`. This is how
`canonLin` is computed, since `canonLin S` is the projection onto the canonical complement
along `S`. -/
theorem projection_eq_of {E : Type*} [AddCommGroup E] [Module F E] {p q : Submodule F E}
    (hpq : IsCompl p q) {x y : E} (hy : y ∈ p) (hxy : x - y ∈ q) :
    p.projection q hpq x = y := by
  have h1 : (p.projection q hpq x : E) - y ∈ p :=
    Submodule.sub_mem _ (Submodule.projection_apply_mem hpq x) hy
  have h2 : (p.projection q hpq x : E) - y ∈ q := by
    have e : (p.projection q hpq x : E) - y = -(x - (p.projection q hpq x : E)) + (x - y) := by
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.sub_projection_mem hpq x)) hxy
  have hbot := hpq.inf_eq_bot
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨h1, h2⟩)
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
theorem _root_.solution {w : Fin n → F} (hw : ∃ j, w j ≠ 0) (x : Fin n → F) :
    canonLin (span F {w}) x
      = x - (x (Fin.find (fun j => w j ≠ 0) hw)
          / w (Fin.find (fun j => w j ≠ 0) hw)) • w := by
  classical
  set p := Fin.find (fun j => w j ≠ 0) hw with hp
  have hwp : w p ≠ 0 := Fin.find_spec hw
  refine projection_eq_of (isCompl_canonCompl (span F {w})).symm ?_ ?_
  · rw [canonCompl, mem_coordSub]
    intro i hi
    rw [pivots_span_singleton hw, Finset.mem_singleton] at hi
    subst hi
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hwp, sub_self]
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
end MIPRE.LIDT.Adapter
