-- Prove2me | solution 1 for MIPRE.SAT.Circuit.evalBits_factorBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:26.428503+00:00
-- url     : https://prove2.me/submissions/fe0a0058-14b8-4de9-aa3e-2f6ef38fedbd

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitFieldCorrect.lean (solution of MIPRE.SAT.Circuit.evalBits_factorBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
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
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldEval
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldCorrect
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_SAT_Circuit_evalBits_gateBits
import Theorems.Thm_MIPRE_SAT_Circuit_length_gateBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial
theorem evalBits_oneBits {R : Type*} [CommRing R] (z : R) (p : BitStr) (hp : p ≠ []) :
    BinaryPolynomial.evalBits z (oneBits p) = 1 := BinaryPolynomial.evalBits_oneBits z p hp
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R]
theorem gateValue_eq_eval_gateArith {F : Type*} [Field F] [CharP F 2]
    (C : Circuit) (k : ℕ) (g : Gate) (x w : ℕ → F) :
    gateValue (fun i => Sum.elim x w (C.inputRef k i)) w g =
      MvPolynomial.eval (Sum.elim x w) (C.gateArith k g) := by
  cases g <;> simp [gateValue, gateArith, CharTwo.sub_eq_add]
end
end MIPRE.SAT.Circuit

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
variable {F : Type*} [Field F] [CharP F 2]
theorem _root_.solution (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k < C.size) :
    BinaryPolynomial.evalBits z (factorBits (p, x, w, C.fieldHistory w k)
      (C.gates.getD k (.const false), w.getD k [])) =
      MvPolynomial.eval (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i []))
        (fun j => BinaryPolynomial.evalBits z (w.getD j []))) (C.consistencyFactor k) := by
  have hr := gate_ref_width C hC p w hwlen hw k hk
  have hi := gate_input_width C hC p x w hxlen hwlen hx hw k hk
  have hg := length_gateBits p (readInput (p, x, w, C.fieldHistory w k)) w
    (C.gates.getD k (.const false)) hi hr
  have hkwidth := width_getD p w hw k (hk.trans_le hwlen)
  have hl : (xorBits (oneBits p) (w.getD k [])).length = p.length := by
    simp only [length_xorBits, length_oneBits, hkwidth, min_self]
  unfold factorBits
  change BinaryPolynomial.evalBits z (xorBits (xorBits (oneBits p) (w.getD k []))
    (gateBits p (readInput (p, x, w, C.fieldHistory w k)) w
      (C.gates.getD k (.const false)))) = _
  rw [evalBits_xor z _ _ (hl.trans hg.symm),
    evalBits_xor z _ _ (by simpa using hkwidth.symm), evalBits_oneBits z p hp,
    evalBits_gateBits z p hp hroot _ _ _ hr]
  have he : (fun i => BinaryPolynomial.evalBits z (readInput (p, x, w, C.fieldHistory w k) i)) =
      (fun i => Sum.elim (fun j => BinaryPolynomial.evalBits z (x.getD j []))
        (fun j => BinaryPolynomial.evalBits z (w.getD j [])) (C.inputRef k i)) := by
    funext i
    rw [readInput_fieldHistory]
    cases C.inputRef k i <;> rfl
  rw [he, gateValue_eq_eval_gateArith]
  simp [consistencyFactor]
end MIPRE.SAT.Circuit
