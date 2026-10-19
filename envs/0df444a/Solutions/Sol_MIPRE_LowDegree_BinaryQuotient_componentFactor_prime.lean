-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.componentFactor_prime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:24:42.219772+00:00
-- url     : https://prove2.me/submissions/7ad09c66-bf48-4333-b1c6-aad5a7c974ad

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean (solution of MIPRE.LowDegree.BinaryQuotient.componentFactor_prime);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_componentFactor_dvd_iff
import Theorems.Thm_MIPRE_LowDegree_PrimitiveBinaryComponent_exists_mul_eq

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Polynomial
theorem _root_.solution (f E : Polynomial (ZMod 2)) (hf : f ≠ 0)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (he : PrimitiveBinaryComponent (AdjoinRoot.mk f E)) :
    Prime (componentFactor f E) := by
  have hne : componentFactor f E ≠ 0 :=
    ne_zero_of_dvd_ne_zero hf (gcd_dvd_left f (E - 1))
  have hunit : ¬ IsUnit (componentFactor f E) := by
    intro hu
    have hz := (componentFactor_dvd_iff f E 1 he.2.1).mp (isUnit_iff_dvd_one.mp hu)
    exact he.1 (by simpa only [map_one, mul_one] using hz)
  refine ⟨hne, hunit, ?_⟩
  intro U V huv
  by_cases hu : componentFactor f E ∣ U
  · exact Or.inl hu
  · right
    have hU : AdjoinRoot.mk f E * AdjoinRoot.mk f U ≠ 0 := by
      intro h
      exact hu ((componentFactor_dvd_iff f E U he.2.1).mpr h)
    have hEU : AdjoinRoot.mk f E * (AdjoinRoot.mk f E * AdjoinRoot.mk f U) =
        AdjoinRoot.mk f E * AdjoinRoot.mk f U := by rw [← mul_assoc, he.2.1]
    obtain ⟨z, hz⟩ := he.exists_mul_eq hsq _ hU hEU
    have hUV := (componentFactor_dvd_iff f E (U * V) he.2.1).mp huv
    rw [map_mul] at hUV
    apply (componentFactor_dvd_iff f E V he.2.1).mpr
    calc
      AdjoinRoot.mk f E * AdjoinRoot.mk f V =
          (AdjoinRoot.mk f E * AdjoinRoot.mk f U * z) * AdjoinRoot.mk f V := by rw [hz]
      _ = z * (AdjoinRoot.mk f E * (AdjoinRoot.mk f U * AdjoinRoot.mk f V)) := by ring
      _ = 0 := by rw [hUV, mul_zero]
end MIPRE.LowDegree.BinaryQuotient
