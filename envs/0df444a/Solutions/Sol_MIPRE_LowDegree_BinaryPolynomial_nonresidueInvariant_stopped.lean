-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.nonresidueInvariant_stopped
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:09:14.82298+00:00
-- url     : https://prove2.me/submissions/5517e345-8661-4a26-8d13-66658f73040c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryNonresidueCorrectness.lean (solution of MIPRE.LowDegree.BinaryPolynomial.nonresidueInvariant_stopped);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- A list with a true leading bit decomposes into its lower coefficients and that bit. -/
theorem dropLast_append_true (a : BitStr) (h : a.getLastD false = true) :
    a.dropLast ++ [true] = a := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hh : a.getLast hn = true := by
    cases a with
    | nil => exact (hn rfl).elim
    | cons b a => simpa only [List.getLast_eq_getLastD, List.getLastD_cons] using h
  simpa only [hh] using List.dropLast_append_getLast hn
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- A coefficient list with leading bit one represents a monic polynomial. -/
theorem monic_polyOfBits_of_getLast (a : BitStr) (h : a.getLastD false = true) :
    (polyOfBits a).Monic := by
  rw [← dropLast_append_true a h]
  exact monic_polyOfBits_append_true _
end
end MIPRE.LowDegree.BinaryPolynomial

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
/-- Canonical quotient coordinates determine the binary quotient cardinality. -/
theorem card_adjoinRoot_binary (f : Polynomial (ZMod 2)) (hf : f.Monic) :
    Nat.card (AdjoinRoot f) = 2 ^ f.natDegree := by
  rw [Nat.card_congr (BinaryQuotient.coordinateEquiv f hf).toEquiv]
  simp
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- The primitive order of a binary root divides its field's multiplicative cardinality. -/
theorem primitive_root_order_dvd_card (f : Polynomial (ZMod 2)) (hf : f.Monic)
    (hi : Irreducible f) (n : ℕ) (hn : n ≠ 0)
    (hr : IsPrimitiveRoot (AdjoinRoot.root f) n) : n ∣ 2 ^ f.natDegree - 1 := by
  let : Fact (Irreducible f) := ⟨hi⟩
  let : Fintype (AdjoinRoot f) :=
    Fintype.ofEquiv (Fin f.natDegree → ZMod 2) (BinaryQuotient.coordinateEquiv f hf).symm.toEquiv
  have hd := hr.dvd_of_pow_eq_one (Fintype.card (AdjoinRoot f) - 1)
    (FiniteField.pow_card_sub_one_eq_one _ (hr.ne_zero hn))
  simpa only [← Nat.card_eq_fintype_card, card_adjoinRoot_binary f hf] using hd
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- An odd prime cannot be lifted more often than the auxiliary binary degree. -/
theorem prime_power_lift_bound (f : Polynomial (ZMod 2)) (hf : f.Monic)
    (hi : Irreducible f) (q s : ℕ) (hq : q.Prime)
    (hr : IsPrimitiveRoot (AdjoinRoot.root f) (q ^ s)) : s ≤ f.natDegree := by
  have hd := primitive_root_order_dvd_card f hf hi (q ^ s) (pow_ne_zero _ hq.ne_zero) hr
  have hpos : 0 < 2 ^ f.natDegree - 1 := by
    have hx : 1 < 2 ^ f.natDegree := one_lt_pow₀ (by decide) hi.natDegree_pos.ne'
    omega
  have hle := Nat.le_of_dvd hpos hd
  have hq2 : 2 ≤ q := hq.two_le
  have hp : 2 ^ s ≤ q ^ s := Nat.pow_le_pow_left hq2 s
  have hlt : 2 ^ s < 2 ^ f.natDegree := by omega
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt |>.le
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Polynomial
theorem _root_.solution (q m i : ℕ) (s : NonresidueState)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s) (hi : m ≤ i) :
    s.2.2.1 = true := by
  by_contra hd
  have hd' : s.2.2.1 = false := Bool.eq_false_iff.mpr hd
  let f := polyOfBits s.2.2.2
  have hf : f.Monic := monic_polyOfBits_of_getLast _ hv.canonical
  let : Fact (Irreducible f) := ⟨hv.irreducible⟩
  let : NeZero ((q ^ (i + 1) : ℕ) : ZMod 2) :=
    ⟨oddPrimePower_cast_ne_zero q (i + 1) hq hq2⟩
  let : NeZero ((q ^ (i + 1) : ℕ) : AdjoinRoot f) :=
    NeZero.of_injective (algebraMap (ZMod 2) (AdjoinRoot f)).injective
  have hr : IsPrimitiveRoot (AdjoinRoot.root f) (q ^ (i + 1)) :=
    primitiveRoot_of_aeval_dvd_cyclotomic f _ (hv.running hd') _ (by simp)
  have hb := prime_power_lift_bound f hf hv.irreducible q (i + 1) hq hr
  change i + 1 ≤ (polyOfBits s.2.2.2).natDegree at hb
  rw [hv.degree] at hb
  omega
end MIPRE.LowDegree.BinaryPolynomial
