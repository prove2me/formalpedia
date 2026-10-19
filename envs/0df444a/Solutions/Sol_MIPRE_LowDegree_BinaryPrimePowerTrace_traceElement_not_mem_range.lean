-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_not_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:09:16.261989+00:00
-- url     : https://prove2.me/submissions/c7bcf6f1-6bd3-4a59-9f86-9777fb7c1dc1

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPrimePowerTrace.lean (solution of MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_not_mem_range);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPrimePowerTrace
open Polynomial IntermediateField
theorem _root_.solution {L E : Type*} [Field L] [Field E] [Algebra L E]
    (β : E) (w : L) (m r q : ℕ) (hm : 0 < m) (hq : 1 < q)
    (hw : algebraMap L E w = β ^ q)
    (hinj : Function.Injective (fun i : Fin m => 2 ^ (r * (i : ℕ)) % q))
    (hdeg : q ≤ (minpoly L β).natDegree) :
    traceElement β m r ∉ (algebraMap L E).range := by
  classical
  rintro ⟨c, hc⟩
  let A : (Fin m) → L[X] := fun i =>
    C (w ^ (2 ^ (r * (i : ℕ)) / q)) * X ^ (2 ^ (r * (i : ℕ)) % q)
  let P : L[X] := (∑ i : Fin m, A i) - C c
  let i₀ : Fin m := ⟨0, hm⟩
  have hres₀ : 2 ^ (r * (i₀ : ℕ)) % q = 1 := by
    simp only [i₀, Nat.mul_zero, pow_zero, Nat.mod_eq_of_lt hq]
  have hcoeff : P.coeff 1 = 1 := by
    change ((∑ i : Fin m, A i) - C c).coeff 1 = 1
    rw [coeff_sub, finsetSum_coeff, coeff_C]
    simp only [one_ne_zero, ↓reduceIte, sub_zero]
    rw [Finset.sum_eq_single i₀]
    · simp [A, i₀, Nat.mod_eq_of_lt hq, Nat.div_eq_of_lt hq]
    · intro j _ hj
      have hr : 2 ^ (r * (j : ℕ)) % q ≠ 1 := by
        intro he
        exact hj (hinj (he.trans hres₀.symm))
      change (C (w ^ (2 ^ (r * (j : ℕ)) / q)) * X ^ (2 ^ (r * (j : ℕ)) % q)).coeff 1 = 0
      simp only [coeff_C_mul_X_pow, Ne.symm hr, if_false]
    · simp
  have hP : P ≠ 0 := by intro he; simp [he] at hcoeff
  have hPdeg : P.degree < (q : WithBot ℕ) := by
    change ((∑ i : Fin m, A i) - C c).degree < _
    apply (degree_sub_le _ _).trans_lt
    apply max_lt
    · apply (degree_sum_le _ _).trans_lt
      apply (Finset.sup_lt_iff (WithBot.bot_lt_coe q)).2
      intro i _
      exact (degree_C_mul_X_pow_le _ _).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.mod_lt _ (by omega)))
    · exact degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr (show 0 < q by omega))
  have heval (i : Fin m) : aeval β (A i) = β ^ (2 ^ (r * (i : ℕ))) := by
    simp only [A, map_mul, aeval_C, map_pow, aeval_X, hw, ← pow_mul, ← pow_add]
    congr 1
    exact Nat.div_add_mod _ _
  have hz : aeval β P = 0 := by
    change aeval β ((∑ i : Fin m, A i) - C c) = 0
    rw [map_sub, map_sum]
    simp only [heval, aeval_C, hc, traceElement, sub_self]
  have hle := natDegree_le_of_dvd (minpoly.dvd L β hz) hP
  have hlt : P.natDegree < q := (natDegree_lt_iff_degree_lt (by omega)).mpr hPdeg
  omega
end MIPRE.LowDegree.BinaryPrimePowerTrace
