-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree_of_root_degrees
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:12:28.583982+00:00
-- url     : https://prove2.me/submissions/dd335d17-6748-42aa-9031-9c62c92c5e06

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPrimePowerTrace.lean (solution of MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree_of_root_degrees);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPrimePowerTrace_traceElement_natDegree

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryFiniteField
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
/-- Binary minimal degree divides exactly the Frobenius periods of an integral element. -/
theorem minpoly_natDegree_dvd_iff_frobenius (x : L) (hx : IsIntegral (ZMod 2) x) (n : ℕ) :
    (minpoly (ZMod 2) x).natDegree ∣ n ↔ x ^ (2 ^ n) = x := by
  rw [(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  simp only [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card, ZMod.card, sub_eq_zero]
end
end MIPRE.LowDegree.BinaryFiniteField

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPrimePowerTrace
open Polynomial IntermediateField
theorem _root_.solution {E : Type*} [Field E] [Finite E]
    [Algebra (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (β : E) (m q e : ℕ) (hm : 0 < m) (hq : q.Prime)
    (horder : orderOf (2 : ZMod q) = m) (hcop : q.Coprime m)
    (hprim : IntermediateField.adjoin (ZMod 2) ({β} : Set E) = ⊤)
    (hβ : (minpoly (ZMod 2) β).natDegree = m * q ^ (e + 1))
    (hβq : (minpoly (ZMod 2) (β ^ q)).natDegree = m * q ^ e) :
    (minpoly (ZMod 2) (traceElement β m (q ^ (e + 1)))).natDegree = q ^ (e + 1) := by
  let L := IntermediateField.adjoin (ZMod 2) ({β ^ q} : Set E)
  let w : L := ⟨β ^ q, IntermediateField.subset_adjoin (ZMod 2) _ (by simp)⟩
  have hi : IsIntegral (ZMod 2) β := IsIntegral.of_finite (ZMod 2) β
  have hdim : Module.finrank (ZMod 2) E = m * q ^ (e + 1) := by
    rw [← hβ, ← IntermediateField.adjoin.finrank hi, hprim, finrank_top']
  have hL : Module.finrank (ZMod 2) L = m * q ^ e := by
    rw [IntermediateField.adjoin.finrank (hi.pow q), hβq]
  have hprimL : IntermediateField.adjoin L ({β} : Set E) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top (ZMod 2) hprim
  have hrdeg : (minpoly L β).natDegree = Module.finrank L E := by
    rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite L β), hprimL, finrank_top']
  have hmul : (m * q ^ e) * Module.finrank L E = (m * q ^ e) * q := by
    have h := Module.finrank_mul_finrank (ZMod 2) L E
    rw [hL, hdim] at h
    simpa only [pow_succ, Nat.mul_assoc] using h
  have hrank : Module.finrank L E = q :=
    Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hm (pow_pos hq.pos e)) hmul
  have hcard : Nat.card L = 2 ^ (m * q ^ e) := by
    let : Fintype L := Fintype.ofFinite L
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hL]
  have hclosed : β ^ (2 ^ (q ^ (e + 1) * m)) = β :=
    (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius β hi _).1
      (by rw [hβ, Nat.mul_comm])
  exact traceElement_natDegree β w m q e hm hq rfl horder hcop hcard
    (by rw [hrdeg, hrank]) hclosed
end MIPRE.LowDegree.BinaryPrimePowerTrace
