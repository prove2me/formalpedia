-- Prove2me | solution 1 for MIPRE.SAT.answerVec_injective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:31.957318+00:00
-- url     : https://prove2.me/submissions/f4bdc474-eb1e-4a8c-b28b-02cae98b2fa9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/AnswerVec.lean (solution of MIPRE.SAT.answerVec_injective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Theorems.Thm_MIPRE_SAT_exists_bitsVal_ofFn

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT
section
open Cost LowDegree
theorem cellBits_injective : Function.Injective cellBits := by
  intro a b h
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> first | rfl | simp [cellBits] at h
end
end MIPRE.SAT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT
open Cost LowDegree
theorem _root_.solution {F : Type*} [CommRing F] [Nontrivial F] (m : ℕ) {a b : BitStr}
    (ha : 2 * a.length ≤ 2 ^ m) (hb : 2 * b.length ≤ 2 ^ m)
    (h : answerVec F m a = answerVec F m b) : a = b := by
  have hofBool : Function.Injective (ofBool : Bool → F) := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [ofBool]
  have htape : ∀ p < 2 ^ m, tapeBits a p = tapeBits b p := by
    intro p hp
    obtain ⟨w, hw⟩ := exists_bitsVal_ofFn m p hp
    have := congrFun h w
    simp only [answerVec, hw] at this
    exact hofBool this
  refine List.ext_getElem? fun c => ?_
  by_cases hc : 2 * c + 1 < 2 ^ m
  · have h0 := htape (2 * c) (by omega)
    have h1 := htape (2 * c + 1) hc
    simp only [tapeBits, Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left _ two_pos] at h0
    have hodd : (2 * c + 1) % 2 = 1 := by omega
    have hdiv : (2 * c + 1) / 2 = c := by omega
    simp only [tapeBits, hodd, hdiv] at h1
    simp only [one_ne_zero, if_false] at h1
    exact cellBits_injective (Prod.ext h0 h1)
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
end MIPRE.SAT
