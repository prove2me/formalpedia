-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.componentFactors_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:02.319023+00:00
-- url     : https://prove2.me/submissions/30f44e78-546b-4fbf-8171-ec206a2aab18

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean (solution of MIPRE.LowDegree.BinaryQuotient.componentFactors_list_prod);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
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
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_componentFactors_prod

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Polynomial
theorem _root_.solution (f : Polynomial (ZMod 2)) (hf : f.Monic)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (l : List (Polynomial (ZMod 2)))
    (hl : ComponentFamily (l.map (AdjoinRoot.mk f)))
    (he : ∀ E ∈ l, PrimitiveBinaryComponent (AdjoinRoot.mk f E)) :
    (l.map (componentFactor f)).prod = f := by
  have hpair : l.Pairwise (fun E H => AdjoinRoot.mk f E * AdjoinRoot.mk f H = 0) :=
    List.pairwise_map.mp hl.orthogonal
  have horth : Pairwise (fun i j : Fin l.length =>
      AdjoinRoot.mk f (l.get i) * AdjoinRoot.mk f (l.get j) = 0) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpair.rel_get_of_lt h
    · rw [mul_comm]
      exact hpair.rel_get_of_lt h
  have hsum : (∑ i : Fin l.length, AdjoinRoot.mk f (l.get i)) = 1 := by
    simpa only [List.get_eq_getElem, Fin.sum_univ_fun_getElem] using hl.sum_eq_one
  have hp := componentFactors_prod f hf hsq (fun i : Fin l.length => l.get i)
    (fun i => he _ (List.get_mem l i)) horth hsum
  simpa only [List.get_eq_getElem, Fin.prod_univ_fun_getElem] using hp
end MIPRE.LowDegree.BinaryQuotient
