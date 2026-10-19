-- Prove2me | solution 1 for MIPRE.Pipeline.PDom.ofCallPow
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:07.568644+00:00
-- url     : https://prove2.me/submissions/27490d95-b83d-4b3b-88ea-502262c69040

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/PowDom.lean (solution of MIPRE.Pipeline.PDom.ofCallPow);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- A base of at least one is below its `(K + 1)`-st power. -/
theorem le_pow_succ {a : ℕ} : a ≤ a ^ (K + 1) :=
  Nat.le_self_pow (by omega) a
end
end MIPRE.Pipeline.PDom

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Pipeline.PDom
open Cost
variable {W X K : ℕ}
theorem _root_.solution {B q t c₀ m₀ c₁ m₁ e₁ e' : ℕ} (hB : B ≤ c₀ * (W + 1) ^ m₀)
    (hq : q + 1 ≤ c₁ * (W + 1) ^ m₁ * X ^ e₁) (ht : t ≤ B * (q + 1) ^ (e' * (K + 1))) :
    PDom W X K (c₀ * c₁ ^ e') (m₀ + m₁ * e') (e₁ * e') t := by
  unfold PDom
  refine ht.trans ?_
  calc B * (q + 1) ^ (e' * (K + 1))
      ≤ c₀ * (W + 1) ^ m₀ * ((c₁ * (W + 1) ^ m₁ * X ^ e₁) ^ e') ^ (K + 1) := by
        rw [← pow_mul]
        exact Nat.mul_le_mul hB (Nat.pow_le_pow_left hq _)
    _ ≤ (c₀ * (W + 1) ^ m₀) ^ (K + 1) * ((c₁ * (W + 1) ^ m₁ * X ^ e₁) ^ e') ^ (K + 1) :=
        Nat.mul_le_mul_right _ le_pow_succ
    _ = (c₀ * c₁ ^ e' * (W + 1) ^ (m₀ + m₁ * e') * X ^ (e₁ * e')) ^ (K + 1) := by
        rw [← mul_pow]
        congr 1
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
        ring
end MIPRE.Pipeline.PDom
