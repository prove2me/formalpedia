-- Prove2me | solution 1 for MIPRE.SAT.Fml.eval_addConstRel_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:55.69675+00:00
-- url     : https://prove2.me/submissions/65c8473e-f866-4fe8-a9e3-81205d96e381

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FmlLib.lean (solution of MIPRE.SAT.Fml.eval_addConstRel_iff);
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
import Theorems.Thm_MIPRE_SAT_Fml_val_addBits
import Theorems.Thm_MIPRE_SAT_bitsVal_injective
import Theorems.Thm_MIPRE_SAT_bitsVal_lt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_xnor (f g : Fml) (x : ℕ → Bool) : (xnor f g).eval x = (f.eval x == g.eval x) := by
  simp only [xnor, eval]; cases f.eval x <;> cases g.eval x <;> rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_lt (fs : List Fml) (x : ℕ → Bool) : val fs x < 2 ^ fs.length := by
  have := bitsVal_lt (bitsOf fs x); rwa [length_bitsOf] at this
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_foldl_eqFStep : ∀ (fs gs : List Fml), fs.length = gs.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      ((fs.zip gs).foldl eqFStep init).eval x = (init.eval x && decide (bitsOf fs x = bitsOf gs x))
  | [], [], _, init, x => by simp
  | f :: fs, g :: gs, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_eqFStep fs gs h]
    simp only [eqFStep, eval, bitsOf_cons, List.cons.injEq, Bool.decide_and, eval_xnor]
    cases hg : g.eval x <;> cases hf : f.eval x <;> simp [hf, hg, Bool.and_assoc]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_eqFields (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = decide (bitsOf fs x = bitsOf gs x) := by
  rw [eqFields, eval_foldl_eqFStep fs gs h]; rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_eqFields_iff (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = true ↔ val fs x = val gs x := by
  rw [eval_eqFields fs gs h, decide_eq_true_iff, val, val]
  constructor
  · intro e; rw [e]
  · intro hv; exact bitsVal_injective (by simp [h]) hv
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem length_addBits : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length → ∀ cin,
    (addBits fs c cin).1.length = fs.length
  | [], [], _, _ => rfl
  | f :: fs, b :: c, h, cin => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [addBits, length_addBits fs c h]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem length_addConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) :
    (addConstBits fs c).length = fs.length := length_addBits fs c h _
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_addConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    val (addConstBits fs c) x + 2 ^ fs.length * ((addConstCarry fs c).eval x).toNat =
      val fs x + bitsVal c := by
  have := val_addBits fs c h (const false) x
  simpa [addConstBits, addConstCarry, eval] using this
end
end MIPRE.SAT.Fml

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
open Cost
theorem _root_.solution (fs gs : List Fml) (c : BitStr) (h : fs.length = c.length)
    (hg : gs.length = fs.length) (x : ℕ → Bool) :
    (addConstRel fs gs c).eval x = true ↔ val gs x = val fs x + bitsVal c := by
  have hid := val_addConstBits fs c h x
  have hlen := length_addConstBits fs c h
  simp only [addConstRel, eval, Bool.and_eq_true, Bool.not_eq_true',
    eval_eqFields_iff gs (addConstBits fs c) (by omega)]
  have hg' := val_lt gs x
  rw [hg] at hg'
  constructor
  · rintro ⟨h1, h2⟩; rw [h2] at hid; simp at hid; omega
  · intro hv
    cases hc : (addConstCarry fs c).eval x
    · rw [hc] at hid; simp at hid; exact ⟨by omega, rfl⟩
    · rw [hc] at hid; simp at hid; exfalso; omega
end MIPRE.SAT.Fml
