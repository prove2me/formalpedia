-- Prove2me | solution 1 for MIPRE.SAT.bitsVal_injective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:10.617336+00:00
-- url     : https://prove2.me/submissions/68c24483-eac6-47e0-9fc0-d52771467932

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FmlLib.lean (solution of MIPRE.SAT.bitsVal_injective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT
section
open Cost
theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]
end
end MIPRE.SAT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT
open Cost
theorem _root_.solution : ∀ {l₁ l₂ : BitStr}, l₁.length = l₂.length → bitsVal l₁ = bitsVal l₂ →
    l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, hv => by
    rw [bitsVal_cons', bitsVal_cons'] at hv
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hb : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> simp at hv ⊢ <;> omega
    subst hb
    have : bitsVal l₁ = bitsVal l₂ := by cases b₁ <;> simp at hv <;> omega
    rw [solution hl this]
end MIPRE.SAT
