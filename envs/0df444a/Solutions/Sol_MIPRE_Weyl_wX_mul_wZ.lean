-- Prove2me | solution 1 for MIPRE.Weyl.wX_mul_wZ
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:34:53.990628+00:00
-- url     : https://prove2.me/submissions/9c111dc5-819f-4498-9836-db4a277eb7d2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Weyl.lean (solution of MIPRE.Weyl.wX_mul_wZ);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
theorem sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  rw [sgn]; split_ifs <;> norm_num
end
end MIPRE

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_comm (a b : n → F) : trDot a b = trDot b a := by
  rw [trDot, trDot, Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_add_right (a b b' : n → F) : trDot a (b + b') = trDot a b + trDot a b' := by
  rw [trDot_comm, trDot_add_left, trDot_comm b a, trDot_comm b' a]
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem _root_.solution (a b : n → F) :
    wX a * wZ b = sgn (trDot a b) • (wZ b * wX a) := by
  ext j i
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply]
  -- the left product picks out `k = i`, the right one `k = j`
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [show wZ b k i = 0 from by rw [wZ_apply, if_neg hk], mul_zero])
    fun h => absurd (Finset.mem_univ _) h]
  rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [show wZ b j k = 0 from by rw [wZ_apply, if_neg (Ne.symm hk)], zero_mul])
    fun h => absurd (Finset.mem_univ _) h]
  rw [wZ_apply, if_pos rfl, wZ_apply, if_pos rfl, smul_eq_mul, wX_apply]
  by_cases h : j = i + a
  · rw [if_pos h, one_mul, mul_one, h, trDot_add_right, sgn_add, trDot_comm a b,
      mul_comm (sgn (trDot b i)) (sgn (trDot b a)), ← mul_assoc, sgn_mul_self, one_mul]
  · rw [if_neg h, zero_mul, mul_zero, mul_zero]
end MIPRE.Weyl
