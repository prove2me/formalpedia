-- Prove2me | solution 1 for MIPRE.SAT.Circuit.length_gateBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:24:42.815747+00:00
-- url     : https://prove2.me/submissions/19390474-ab25-46c4-8c9f-39bcd196b797

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/GateFieldEval.lean (solution of MIPRE.SAT.Circuit.length_gateBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R]
theorem _root_.solution (p : BitStr) (x : ℕ → BitStr) (w : List BitStr) (g : Gate)
    (hx : ∀ i, g = .input i → (x i).length = p.length)
    (hw : ∀ j ∈ g.refs, (w.getD j []).length = p.length) :
    (gateBits p x w g).length = p.length := by
  cases g with
  | input i => exact hx i rfl
  | const b => cases b <;> simp [gateBits]
  | and u v => exact length_mulReduce p _ _ (hw u (by simp [Gate.refs]))
  | or u v =>
    have hu := hw u (by simp [Gate.refs])
    have ha : (xorBits (oneBits p) (w.getD u [])).length = p.length := by
      simp only [length_xorBits, length_oneBits, hu, min_self]
    simp only [gateBits, length_xorBits, length_oneBits, length_mulReduce p _ _ ha, min_self]
  | not u =>
    simp only [gateBits, length_xorBits, length_oneBits, hw u (by simp [Gate.refs]), min_self]
end MIPRE.SAT.Circuit
