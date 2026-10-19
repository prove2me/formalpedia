-- Prove2me | solution 1 for MIPRE.SAT.Fml.val_addBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:03.437132+00:00
-- url     : https://prove2.me/submissions/beca82fd-744b-40a7-9ab5-05f132837814

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FmlLib.lean (solution of MIPRE.SAT.Fml.val_addBits);
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

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_xor (f g : Fml) (x : ℕ → Bool) : (xor f g).eval x = (f.eval x != g.eval x) := by
  simp only [xor, eval]; cases f.eval x <;> cases g.eval x <;> rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_cons (f : Fml) (fs : List Fml) (x : ℕ → Bool) :
    val (f :: fs) x = 2 * val fs x + (f.eval x).toNat := by
  simp only [val, bitsOf_cons]; rw [bitsVal_cons']
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_sum3_maj3 (f b c : Fml) (x : ℕ → Bool) :
    ((sum3 f b c).eval x).toNat + 2 * ((maj3 f b c).eval x).toNat =
      (f.eval x).toNat + (b.eval x).toNat + (c.eval x).toNat := by
  simp only [sum3, maj3, eval_xor, eval]
  cases f.eval x <;> cases b.eval x <;> cases c.eval x <;> rfl
end
end MIPRE.SAT.Fml

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
open Cost
theorem _root_.solution : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length → ∀ (cin : Fml) (x : ℕ → Bool),
    val (addBits fs c cin).1 x + 2 ^ fs.length * ((addBits fs c cin).2.eval x).toNat =
      val fs x + bitsVal c + (cin.eval x).toNat
  | [], [], _, cin, x => by simp [addBits, val, bitsVal_nil]
  | f :: fs, b :: c, h, cin, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := solution fs c h (maj3 f (const b) cin) x
    have hs := eval_sum3_maj3 f (const b) cin x
    simp only [addBits, val_cons, bitsVal_cons', List.length_cons, Nat.pow_succ, eval] at ih hs ⊢
    generalize (sum3 f (const b) cin).eval x = s at *
    generalize (maj3 f (const b) cin).eval x = m at *
    generalize (addBits fs c (maj3 f (const b) cin)).2.eval x = co at *
    generalize val (addBits fs c (maj3 f (const b) cin)).1 x = vr at *
    generalize val fs x = vf at *
    generalize bitsVal c = vc at *
    generalize (f.eval x).toNat = ef at *
    generalize (cin.eval x).toNat = ec at *
    generalize (2 : ℕ) ^ fs.length = P at *
    cases s <;> cases m <;> cases b <;> cases co <;> simp at * <;> omega
end MIPRE.SAT.Fml
