-- Prove2me | solution 1 for MIPRE.SAT.Circuit.evalBits_gateBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:24:43.530982+00:00
-- url     : https://prove2.me/submissions/8320cae1-70db-4fa8-81fd-e591459cdd2e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/GateFieldEval.lean (solution of MIPRE.SAT.Circuit.evalBits_gateBits);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost LowDegree LowDegree.BinaryPolynomial
variable {R : Type*} [CommRing R]
theorem _root_.solution [CharP R 2] (z : R) (p : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = BinaryPolynomial.evalBits z p) (x : ℕ → BitStr) (w : List BitStr) (g : Gate)
    (hw : ∀ j ∈ g.refs, (w.getD j []).length = p.length) :
    BinaryPolynomial.evalBits z (gateBits p x w g) =
      gateValue (fun i => BinaryPolynomial.evalBits z (x i)) (fun j => BinaryPolynomial.evalBits z (w.getD j [])) g := by
  have h1 := evalBits_oneBits z p hp
  cases g with
  | input i => rfl
  | const b => cases b <;> simp [gateBits, gateValue, ofBool, h1]
  | and u v => exact evalBits_mulReduce z p _ _ (hw u (by simp [Gate.refs])) hroot
  | or u v =>
    have hu := hw u (by simp [Gate.refs])
    have hv := hw v (by simp [Gate.refs])
    have hlu : (xorBits (oneBits p) (w.getD u [])).length = p.length := by
      simp only [length_xorBits, length_oneBits, hu, min_self]
    have hlm := length_mulReduce p (xorBits (oneBits p) (w.getD u []))
      (xorBits (oneBits p) (w.getD v [])) hlu
    simp only [gateBits, gateValue]
    rw [evalBits_xor z _ _ (by simpa using hlm.symm),
      evalBits_mulReduce z p _ _ hlu hroot,
      evalBits_xor z _ _ (by simpa using hu.symm),
      evalBits_xor z _ _ (by simpa using hv.symm), h1]
  | not u =>
    simp only [gateBits, gateValue]
    rw [evalBits_xor z _ _ (by simpa using (hw u (by simp [Gate.refs])).symm), h1]
end MIPRE.SAT.Circuit
