-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:44:16.546536+00:00
-- url     : https://prove2.me/submissions/c239b55b-e0c0-406c-8648-e713a205e6f7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryOddPrimeConstructor.lean (solution of MIPRE.LowDegree.BinaryPolynomial.oddPrimePowerBits_correct);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_eval2_polyOfBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_irreducible_comp_prime_pow_of_nonresidue
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_nonresidueLiftBitsProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_oddExtensionLowerBits_spec
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_oddTraceBits_natDegree
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_eval_orbitPolynomial
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_map_orbitPolynomialBits
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_orbitPolynomialBits_monic_natDegree

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
/-- The polynomial used by Shoup's contract reads the same coefficient bits. -/
theorem coeff_polyOfBits (l : BitStr) (i : ℕ) :
    (polyOfBits l).coeff i = ofBool (l.getD i false) := by
  simp only [polyOfBits, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i < l.length
  · simp [hi, ofBool]
  · simp [hi, ofBool, List.getD_eq_getElem?_getD]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
theorem polyOfBits_cons (b : Bool) (l : BitStr) :
    polyOfBits (b :: l) = Polynomial.C (ofBool b) + Polynomial.X * polyOfBits l := by
  ext i
  cases i <;> simp [coeff_polyOfBits, Polynomial.coeff_X_mul]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
variable {R : Type*} [CommRing R]
theorem evalBits_append (z : R) (a b : BitStr) :
    evalBits z (a ++ b) = evalBits z a + z ^ a.length * evalBits z b := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append, evalBits_cons, ih, List.length_cons, pow_succ]; ring
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Suppression of high zero coefficients preserves evaluation in every ring. -/
theorem evalBits_normalizeStep {R : Type*} [CommRing R] (z : R) (a : BitStr) (b : Bool) :
    evalBits z (normalizeStep a b) = ofBool b + z * evalBits z a := by
  cases b <;> cases a <;> simp [normalizeStep, ofBool]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Normalization preserves Horner evaluation. -/
theorem evalBits_normalizeBits {R : Type*} [CommRing R] (z : R) (a : BitStr) :
    evalBits z (normalizeBits a) = evalBits z a := by
  induction a with
  | nil => rfl
  | cons b a ih => rw [normalizeBits_cons, evalBits_normalizeStep, ih, evalBits_cons]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The polynomial interpretation is Horner evaluation at the indeterminate. -/
theorem polyOfBits_eq_evalBits (a : BitStr) :
    polyOfBits a = evalBits (X : Polynomial (ZMod 2)) a := by
  induction a with
  | nil => simp [polyOfBits]
  | cons b a ih =>
    rw [polyOfBits_cons, evalBits_cons, ih]
    cases b <;> simp [ofBool]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Normalization preserves the polynomial itself. -/
theorem polyOfBits_normalizeBits (a : BitStr) :
    polyOfBits (normalizeBits a) = polyOfBits a := by
  simpa only [polyOfBits_eq_evalBits] using evalBits_normalizeBits (X : Polynomial (ZMod 2)) a
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- A nonempty normalized list has a leading coefficient equal to one. -/
theorem normalizeBits_getLast (a : BitStr) :
    normalizeBits a = [] ∨ (normalizeBits a).getLastD false = true := by
  induction a with
  | nil => exact Or.inl rfl
  | cons b a ih =>
    rcases ih with h | h
    · cases b <;> simp [normalizeBits_cons, normalizeStep, h]
    · have hn : normalizeBits a ≠ [] := by intro he; simp [he] at h
      cases ha : normalizeBits a with
      | nil => exact (hn ha).elim
      | cons c a =>
        cases b <;> simpa [normalizeBits_cons, normalizeStep, ha, List.getLastD_cons] using h
end
end MIPRE.LowDegree.BinaryPolynomial

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
section
open Cost Polynomial
/-- Normalizing produces the empty list exactly when the polynomial is zero. -/
theorem normalizeBits_eq_nil_iff (a : BitStr) :
    normalizeBits a = [] ↔ polyOfBits a = 0 := by
  constructor
  · intro h
    rw [← polyOfBits_normalizeBits a, h]
    simp [polyOfBits]
  · intro h
    rcases normalizeBits_getLast a with hn | hn
    · exact hn
    · have hm := monic_polyOfBits_of_getLast _ hn
      rw [polyOfBits_normalizeBits, h] at hm
      exact (hm.ne_zero rfl).elim
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- Substitution has the expected Horner semantics in every commutative ring. -/
theorem evalBits_substitutePowerBits {R : Type*} [CommRing R] (z : R) (a : BitStr) (u : Unary) :
    evalBits z (substitutePowerBits a u) = evalBits (z ^ (u.length + 1)) a := by
  rw [substitutePowerBits, evalBits_normalizeBits]
  induction a with
  | nil => rfl
  | cons b a ih =>
    rw [List.flatMap_cons, evalBits_append, ih]
    simp [evalBits_cons]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- The executable substitution agrees with Mathlib polynomial composition. -/
theorem polyOfBits_substitutePowerBits (a : BitStr) (u : Unary) :
    polyOfBits (substitutePowerBits a u) = (polyOfBits a).comp (X ^ (u.length + 1)) := by
  rw [polyOfBits_eq_evalBits, evalBits_substitutePowerBits]
  exact (eval2_polyOfBits Polynomial.C (X ^ (u.length + 1)) a).symm
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Repeated squaring preserves the fixed-width representation. -/
theorem iterate_squareStep_width (n : ℕ) (p a : BitStr) (ha : a.length = p.length) :
    (squareStep^[n] (p, a)).2.length = p.length := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (length_mulReduce p a a ha)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- The modulus width is preserved on valid quotient elements. -/
theorem frobeniusBits_width (u : Unary) (p a : BitStr) (ha : a.length = p.length) :
    (frobeniusBits u p a).length = p.length := iterate_squareStep_width u.length p a ha
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- Both active coefficient vectors retain the modulus width. -/
theorem fold_traceStep_width (u r : Unary) (p c a : BitStr)
    (hc : c.length = p.length) (ha : a.length = p.length) :
    (u.foldl traceStep (r, p, c, a)).2.2.1.length = p.length ∧
    (u.foldl traceStep (r, p, c, a)).2.2.2.length = p.length := by
  induction u generalizing c a with
  | nil => exact ⟨hc, ha⟩
  | cons b u ih =>
    exact ih _ _ (by simp [length_xorBits, hc, ha]) (frobeniusBits_width r p a ha)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- The modular trace output has exactly the field representation width. -/
theorem traceBits_width (m r : Unary) (p a : BitStr) (ha : a.length = p.length) :
    (traceBits m r p a).length = p.length :=
  (fold_traceStep_width m r p (zeroBits p) a (length_zeroBits p) ha).1
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
/-- When the orbit length is the element's exact degree, the program prints its minimal polynomial. -/
theorem orbitPolynomialBits_eq_minpoly [Fact (Irreducible f)]
    (u : Unary) (p a : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) (hu : 0 < u.length)
    (hdegree : (minpoly (ZMod 2) (evalBits (AdjoinRoot.root f) a)).natDegree = u.length) :
    polyOfBits (orbitPolynomialBits u p a) = minpoly (ZMod 2) (evalBits (AdjoinRoot.root f) a) := by
  let : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have hm := map_orbitPolynomialBits f hf u p a hp hpoly hp0 ha hclosed
  have hz : aeval (evalBits (AdjoinRoot.root f) a) (polyOfBits (orbitPolynomialBits u p a)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hm]
    exact eval_orbitPolynomial _ _ hu
  have hc := orbitPolynomialBits_monic_natDegree f hf u p a hp hpoly hp0 ha hclosed
  have hi : IsIntegral (ZMod 2) (evalBits (AdjoinRoot.root f) a) :=
    ⟨_, hc.1, hz⟩
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hc.1 (minpoly.dvd _ _ hz)
    (by rw [hc.2, hdegree])
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
/-- The exact-degree orbit constructor produces an irreducible binary polynomial. -/
theorem orbitPolynomialBits_irreducible [Fact (Irreducible f)]
    (u : Unary) (p a : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) (hu : 0 < u.length)
    (hdegree : (minpoly (ZMod 2) (evalBits (AdjoinRoot.root f) a)).natDegree = u.length) :
    Irreducible (polyOfBits (orbitPolynomialBits u p a)) := by
  rw [orbitPolynomialBits_eq_minpoly f hf u p a hp hpoly hp0 ha hclosed hu hdegree]
  let : Module.Finite (ZMod 2) (AdjoinRoot f) := hf.finite_adjoinRoot
  apply minpoly.irreducible
  exact IsIntegral.of_finite (ZMod 2) _
end
end MIPRE.LowDegree.BinaryQuotient

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

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryQuotient
/-- The flat printed modulus has the exact Kummer composition semantics. -/
theorem polyOfBits_oddExtensionBits (q r : ℕ) (hr : 0 < r) :
    polyOfBits (oddExtensionBits (unary q) (unary r)) =
      (polyOfBits (nonresidueLiftBitsProg (unary q))).comp (X ^ r) := by
  rw [oddExtensionBits, polyOfBits_substitutePowerBits, List.length_tail, length_unary,
    Nat.sub_add_cancel hr]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryQuotient
/-- The trace vector has exactly the flat extension width. -/
theorem oddTraceBits_width (q r : Unary) :
    (oddTraceBits q r).length = (oddExtensionLowerBits q r).length :=
  traceBits_width _ _ _ _ (BinaryQuotient.length_rootBits _)
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Polynomial BinaryQuotient
theorem _root_.solution (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let a := oddPrimePowerBits (unary q) (unary (q ^ (e + 1)))
    a.getLastD false = true ∧ (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) ∧
      (polyOfBits a).natDegree = q ^ (e + 1) := by
  let f := polyOfBits (nonresidueLiftBitsProg (unary q))
  let F := f.comp (X ^ (q ^ (e + 1)))
  let p := oddExtensionLowerBits (unary q) (unary (q ^ (e + 1)))
  let gamma := oddTraceBits (unary q) (unary (q ^ (e + 1)))
  have ha := nonresidueLiftBitsProg_correct q hq hq2
  have hf : F.Monic := ha.2.1.comp (monic_X.pow _) (by simp [hq.ne_zero])
  let : Fact (Irreducible F) :=
    ⟨irreducible_comp_prime_pow_of_nonresidue f ha.2.1 ha.2.2.1 q (e + 1) hq hq2 ha.2.2.2.2⟩
  let : Module.Finite (ZMod 2) (AdjoinRoot F) := hf.finite_adjoinRoot
  have hs := oddExtensionLowerBits_spec q (e + 1) hq hq2
  have he := polyOfBits_oddExtensionBits q (q ^ (e + 1)) (pow_pos hq.pos _)
  have hpoly : F = polyOfBits (p ++ [true]) := he.symm.trans hs.2.1
  have hp : p.length = F.natDegree := hs.1.trans (congrArg Polynomial.natDegree he)
  have hwidth : gamma.length = p.length := oddTraceBits_width _ _
  have hdegree : (minpoly (ZMod 2) (evalBits (AdjoinRoot.root F) gamma)).natDegree = q ^ (e + 1) :=
    oddTraceBits_natDegree q e hq hq2
  have hclosed : evalBits (AdjoinRoot.root F) gamma ^ (2 ^ (q ^ (e + 1))) =
      evalBits (AdjoinRoot.root F) gamma :=
    (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius _
      (IsIntegral.of_finite (ZMod 2) _) _).mp (by rw [hdegree])
  have hm := orbitPolynomialBits_monic_natDegree F hf (unary (q ^ (e + 1))) p gamma hp hpoly
    hs.2.2 hwidth (by simpa only [length_unary] using hclosed)
  have hi := orbitPolynomialBits_irreducible F hf (unary (q ^ (e + 1))) p gamma hp hpoly
    hs.2.2 hwidth (by simpa only [length_unary] using hclosed)
    (by simpa only [length_unary] using pow_pos hq.pos (e + 1))
    (by simpa only [length_unary] using hdegree)
  let b := orbitPolynomialBits (unary (q ^ (e + 1))) p gamma
  change (normalizeBits b).getLastD false = true ∧ (polyOfBits (normalizeBits b)).Monic ∧
    Irreducible (polyOfBits (normalizeBits b)) ∧
    (polyOfBits (normalizeBits b)).natDegree = q ^ (e + 1)
  rw [polyOfBits_normalizeBits]
  refine ⟨?_, hm.1, hi, by simpa only [length_unary] using hm.2⟩
  rcases normalizeBits_getLast b with hn | hn
  · exact (hm.1.ne_zero ((normalizeBits_eq_nil_iff b).mp hn)).elim
  · exact hn
end MIPRE.LowDegree.BinaryPolynomial
