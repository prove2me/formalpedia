-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.IsPivotBasis.linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:21:13.349977+00:00
-- url     : https://prove2.me/submissions/912eedad-4b3b-40fc-bc00-e26756f684a7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryEchelon.lean (solution of MIPRE.LowDegree.BinaryLinear.IsPivotBasis.linearIndependent);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem pivotVectors_cons (p : Pivot n t) (b : List (Pivot n t)) :
    pivotVectors (p :: b) = Fin.cons p.2.1 (pivotVectors b) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear.IsPivotBasis
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem _root_.solution {b : List (Pivot n t)} (hb : IsPivotBasis b) :
    LinearIndependent (ZMod 2) (pivotVectors b) := by
  induction b with
  | nil =>
    dsimp only [List.length_nil]
    exact linearIndependent_empty_type
  | cons p b ih =>
    rw [pivotVectors_cons]
    apply (linearIndependent_finCons (K := ZMod 2) (v := pivotVectors b) (x := p.2.1)).mpr
    refine ⟨ih hb.2.2, ?_⟩
    let π : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj p.1
    have hs : Submodule.span (ZMod 2) (Set.range (pivotVectors b)) ≤ π.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hb.2.1 b[i] (List.getElem_mem i.isLt)
    intro h
    have hz : p.2.1 p.1 = 0 := hs h
    rw [hb.1] at hz
    exact one_ne_zero hz
end MIPRE.LowDegree.BinaryLinear.IsPivotBasis
