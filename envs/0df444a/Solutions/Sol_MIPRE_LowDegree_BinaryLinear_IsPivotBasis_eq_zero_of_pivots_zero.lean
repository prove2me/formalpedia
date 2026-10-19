-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.IsPivotBasis.eq_zero_of_pivots_zero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:36.147971+00:00
-- url     : https://prove2.me/submissions/96a74f96-7394-4734-bf36-402b04fc889b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySolve.lean (solution of MIPRE.LowDegree.BinaryLinear.IsPivotBasis.eq_zero_of_pivots_zero);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem pivotSpan_cons (p : Pivot n t) (b : List (Pivot n t)) :
    pivotSpan (p :: b) = Submodule.span (ZMod 2) {p.2.1} ⊔ pivotSpan b := by
  have hs : {v | ∃ q ∈ p :: b, q.2.1 = v} =
      insert p.2.1 {v | ∃ q ∈ b, q.2.1 = v} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_cons]
    aesop
  unfold pivotSpan
  rw [hs, Submodule.span_insert]
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear.IsPivotBasis
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem _root_.solution {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) (hz : ∀ p ∈ b, v p.1 = 0) : v = 0 := by
  induction b generalizing v with
  | nil => simpa using hv
  | cons p b ih =>
    rw [pivotSpan_cons] at hv
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hv
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ha
    let π : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj p.1
    have hs : pivotSpan b ≤ π.ker := by
      apply Submodule.span_le.mpr
      rintro w ⟨q, hq, rfl⟩
      exact hb.2.1 q hq
    have hc0 : c p.1 = 0 := hs hc
    have hr0 : r = 0 := by
      have he := congrFun hac p.1
      rw [← hr] at he
      simpa [hb.1, hc0, hz p (by simp)] using he
    rw [hr0, zero_smul] at hr
    have he : c = v := by simpa [← hr] using hac
    subst c
    exact ih hb.2.2 v hc (fun q hq => hz q (by simp [hq]))
end MIPRE.LowDegree.BinaryLinear.IsPivotBasis
