-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.lifted_factor_dvd_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:09:15.455075+00:00
-- url     : https://prove2.me/submissions/6bd77a90-8daf-4807-a516-0bf6570aa4d2

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPrimePowerLift.lean (solution of MIPRE.LowDegree.BinaryPolynomial.lifted_factor_dvd_cyclotomic);
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
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
/-- An odd prime remains nonzero in the binary field. -/
theorem oddPrime_cast_ne_zero (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : (q : ZMod 2) ≠ 0 := by
  intro hz
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) ((CharP.cast_eq_zero_iff (ZMod 2) 2 q).mp hz)
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- Extracting one more prime root increases its prime-power order by exactly one power. -/
theorem primitiveRoot_of_prime_power_root {M : Type*} [CommMonoid M]
    (x : M) (q s : ℕ) (hq : q.Prime) (hs : 0 < s)
    (hx : IsPrimitiveRoot (x ^ q) (q ^ s)) : IsPrimitiveRoot x (q ^ (s + 1)) := by
  have hd : q ^ s ∣ orderOf x := by
    rw [hx.eq_orderOf]
    exact orderOf_pow_dvd q
  have hqdiv : q ∣ orderOf x := (dvd_pow_self q hs.ne').trans hd
  have horder : orderOf x / q = q ^ s := by
    rw [← orderOf_pow_of_dvd hq.ne_zero hqdiv]
    exact hx.eq_orderOf.symm
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rw [pow_succ, ← horder, Nat.div_mul_cancel hqdiv]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- Odd prime powers remain nonzero over the binary field. -/
theorem oddPrimePower_cast_ne_zero (q s : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    ((q ^ s : ℕ) : ZMod 2) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (oddPrime_cast_ne_zero q hq hq2)
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- Any root of a cyclotomic divisor has the prescribed primitive order. -/
theorem primitiveRoot_of_aeval_dvd_cyclotomic {F K : Type*} [Field F] [Field K]
    [Algebra F K] (f : Polynomial F) (n : ℕ) [NeZero (n : K)]
    (hd : f ∣ cyclotomic n F) (z : K) (hz : aeval z f = 0) : IsPrimitiveRoot z n := by
  have hroot : IsRoot (f.map (algebraMap F K)) z := by
    simpa only [IsRoot, eval_map, ← aeval_def] using hz
  have hdiv : f.map (algebraMap F K) ∣ cyclotomic n K := by
    simpa using Polynomial.map_dvd (algebraMap F K) hd
  exact isRoot_cyclotomic_iff.mp (hroot.dvd hdiv)
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- Each factor chosen in a lift advances primitive prime-power order. -/
theorem lifted_root_primitive (f g : Polynomial (ZMod 2)) (q s : ℕ)
    (hq : q.Prime) (hq2 : q ≠ 2) (hs : 0 < s) (hg : Irreducible g)
    (hf : f ∣ cyclotomic (q ^ s) (ZMod 2)) (hd : g ∣ f.comp (X ^ q)) :
    IsPrimitiveRoot (AdjoinRoot.root g) (q ^ (s + 1)) := by
  let : Fact (Irreducible g) := ⟨hg⟩
  let : NeZero ((q ^ s : ℕ) : ZMod 2) := ⟨oddPrimePower_cast_ne_zero q s hq hq2⟩
  let : NeZero ((q ^ s : ℕ) : AdjoinRoot g) :=
    NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot g)).injective
  have hz : aeval (AdjoinRoot.root g ^ q) f = 0 := by
    have hroot : aeval (AdjoinRoot.root g) (f.comp (X ^ q)) = 0 := by
      simpa only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] using hd
    simpa only [aeval_def, eval₂_comp, eval₂_pow, eval₂_X] using hroot
  exact primitiveRoot_of_prime_power_root _ q s hq hs
    (primitiveRoot_of_aeval_dvd_cyclotomic f (q ^ s) hf _ hz)
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Polynomial
theorem _root_.solution (f g : Polynomial (ZMod 2)) (q s : ℕ)
    (hq : q.Prime) (hq2 : q ≠ 2) (hs : 0 < s) (hg : Irreducible g)
    (hf : f ∣ cyclotomic (q ^ s) (ZMod 2)) (hd : g ∣ f.comp (X ^ q)) :
    g ∣ cyclotomic (q ^ (s + 1)) (ZMod 2) := by
  let : Fact (Irreducible g) := ⟨hg⟩
  let : NeZero ((q ^ (s + 1) : ℕ) : ZMod 2) :=
    ⟨oddPrimePower_cast_ne_zero q (s + 1) hq hq2⟩
  let : NeZero ((q ^ (s + 1) : ℕ) : AdjoinRoot g) :=
    NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot g)).injective
  have hp := lifted_root_primitive f g q s hq hq2 hs hg hf hd
  have hr := isRoot_cyclotomic_iff.mpr hp
  have hz : aeval (AdjoinRoot.root g) (cyclotomic (q ^ (s + 1)) (ZMod 2)) = 0 := by
    rw [aeval_def, ← eval_map, Polynomial.map_cyclotomic]
    exact hr
  simpa only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] using hz
end MIPRE.LowDegree.BinaryPolynomial
