-- Prove2me | solution 1 for MIPRE.avg_comp_equiv_fst
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:20:12.752767+00:00
-- url     : https://prove2.me/submissions/9c773eeb-d914-4b70-912b-bd70bc50bc2f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Blocks.lean (solution of MIPRE.avg_comp_equiv_fst);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Blocks

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {A B C D E G M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
  [Fintype G] [AddCommMonoid M]
theorem sum_congr1 {f g : A → M} (h : ∀ a, f a = g a) : ∑ a : A, f a = ∑ a : A, g a :=
  Finset.sum_congr rfl fun a _ => h a
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset
variable {α β F M : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype F]
  [AddCommMonoid M]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α] [Nonempty γ]
theorem _root_.solution (e : α ≃ β × γ) (f : β → ℝ) :
    ∑ a : α, (Fintype.card α : ℝ)⁻¹ * f (e a).1 = ∑ b : β, (Fintype.card β : ℝ)⁻¹ * f b := by
  classical
  have : Nonempty β := ⟨(e (Classical.arbitrary α)).1⟩
  have hcard : Fintype.card α = Fintype.card β * Fintype.card γ := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  have hγ : (Fintype.card γ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Equiv.sum_comp e (fun p : β × γ => (Fintype.card α : ℝ)⁻¹ * f p.1),
    Fintype.sum_prod_type]
  refine sum_congr1 fun b => ?_
  have hb : ∀ c : γ, (Fintype.card α : ℝ)⁻¹ * f ((b, c) : β × γ).1
      = (Fintype.card α : ℝ)⁻¹ * f b := fun _ => rfl
  rw [sum_congr1 hb, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Nat.cast_mul]
  field_simp
end MIPRE
