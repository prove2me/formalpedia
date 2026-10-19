-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.oddTraceBits_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:42:47.023661+00:00
-- url     : https://prove2.me/submissions/a81d27db-6456-414a-81e9-619455d19508

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryOddPrimeConstructor.lean (solution of MIPRE.LowDegree.BinaryPolynomial.oddTraceBits_natDegree);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_cyclotomicSeedBits_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_eval2_polyOfBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oddTraceBits_of_root
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_irreducible_comp_prime_pow_of_nonresidue
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_nonresidueLiftBitsProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_oddExtensionLowerBits_spec
import Theorems.Thm_MIPRE_LowDegree_BinaryPrimePowerTrace_flat_trace_natDegree
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_root_eq

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
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
/-- The seed degree is the multiplicative order of two modulo the odd prime. -/
theorem cyclotomicSeedBits_natDegree (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime 2 q) :
    (polyOfBits (cyclotomicSeedBits (unary q))).natDegree =
      orderOf (ZMod.unitOfCoprime (2 ^ 1) (hcop.pow_left 1)) := by
  have h := cyclotomicSeedBits_correct q hq hq2
  exact natDegree_of_dvd_cyclotomic_of_irreducible
    (show Fintype.card (ZMod 2) = 2 ^ 1 by simp) hcop h.2.2 h.2.1
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
/-- The seed has positive degree dividing `q-1`, so its size is polynomial in unary `q`. -/
theorem cyclotomicSeedBits_degree_dvd (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    0 < (polyOfBits (cyclotomicSeedBits (unary q))).natDegree ∧
      (polyOfBits (cyclotomicSeedBits (unary q))).natDegree ∣ q - 1 := by
  have h := cyclotomicSeedBits_correct q hq hq2
  refine ⟨h.2.1.natDegree_pos, ?_⟩
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  let : NeZero q := ⟨hq.ne_zero⟩
  rw [cyclotomicSeedBits_natDegree q hq hq2 hcop]
  have hd := orderOf_dvd_card (x := ZMod.unitOfCoprime (2 ^ 1) (hcop.pow_left 1))
  simpa only [ZMod.card_units_eq_totient, Nat.totient_prime hq] using hd
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
/-- The seed degree is coprime to the requested odd prime. -/
theorem cyclotomicSeedBits_degree_coprime (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    Nat.Coprime (polyOfBits (cyclotomicSeedBits (unary q))).natDegree q := by
  have h := (cyclotomicSeedBits_degree_dvd q hq hq2).2
  have hc : Nat.Coprime (q - 1) q := by
    have hc : Nat.Coprime (q - 1) ((q - 1) + 1) := by simp
    simpa only [Nat.sub_add_cancel hq.one_le] using hc
  exact hc.of_dvd_left h
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

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- The auxiliary degree is exactly the multiplicative order of two modulo the prime. -/
theorem nonresidueLiftBits_order (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    orderOf (2 : ZMod q) = (polyOfBits (nonresidueLiftBitsProg (unary q))).natDegree := by
  have hcop : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  rw [(nonresidueLiftBitsProg_correct q hq hq2).2.2.2.1,
    cyclotomicSeedBits_natDegree q hq hq2 hcop, ← orderOf_units, ZMod.coe_unitOfCoprime]
  simp
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- The auxiliary degree is coprime to the requested odd prime. -/
theorem nonresidueLiftBits_degree_coprime (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    q.Coprime (polyOfBits (nonresidueLiftBitsProg (unary q))).natDegree := by
  rw [(nonresidueLiftBitsProg_correct q hq hq2).2.2.2.1]
  exact (cyclotomicSeedBits_degree_coprime q hq hq2).symm
end
end MIPRE.LowDegree.BinaryPolynomial

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Polynomial BinaryQuotient
theorem _root_.solution (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let f := polyOfBits (nonresidueLiftBitsProg (unary q))
    let F := f.comp (X ^ (q ^ (e + 1)))
    (minpoly (ZMod 2) (evalBits (AdjoinRoot.root F)
      (oddTraceBits (unary q) (unary (q ^ (e + 1)))))).natDegree = q ^ (e + 1) := by
  let f := polyOfBits (nonresidueLiftBitsProg (unary q))
  let F := f.comp (X ^ (q ^ (e + 1)))
  have ha := nonresidueLiftBitsProg_correct q hq hq2
  have hf : f.Monic := ha.2.1
  have hi : Irreducible f := ha.2.2.1
  let : Fact (Irreducible F) :=
    ⟨irreducible_comp_prime_pow_of_nonresidue f hf hi q (e + 1) hq hq2 ha.2.2.2.2⟩
  let : CharP (AdjoinRoot F) 2 := charP_of_injective_ringHom (AdjoinRoot.of F).injective 2
  let p := oddExtensionLowerBits (unary q) (unary (q ^ (e + 1)))
  have hp := oddExtensionLowerBits_spec q (e + 1) hq hq2
  have he := polyOfBits_oddExtensionBits q (q ^ (e + 1)) (pow_pos hq.pos _)
  have hpoly : F = polyOfBits (p ++ [true]) := he.symm.trans hp.2.1
  have htrace := evalBits_oddTraceBits_of_root (AdjoinRoot.root F) q (e + 1) hq hq2
    (root_eq F p hpoly)
  have hdegree := BinaryPrimePowerTrace.flat_trace_natDegree f hf hi q e hq hq2
    ha.2.2.2.2 (nonresidueLiftBits_order q hq hq2) (nonresidueLiftBits_degree_coprime q hq hq2)
  have htrace' : evalBits (AdjoinRoot.root F)
      (oddTraceBits (unary q) (unary (q ^ (e + 1)))) =
      BinaryPrimePowerTrace.traceElement (AdjoinRoot.root F) f.natDegree (q ^ (e + 1)) := by
    rw [htrace, BinaryPrimePowerTrace.traceElement,
      Fin.sum_univ_eq_sum_range (fun i => AdjoinRoot.root F ^ (2 ^ (q ^ (e + 1) * i)))]
    rw [ha.2.2.2.1]
  change (minpoly (ZMod 2) (evalBits (AdjoinRoot.root F)
    (oddTraceBits (unary q) (unary (q ^ (e + 1)))))).natDegree = _
  rw [htrace']
  exact hdegree
end MIPRE.LowDegree.BinaryPolynomial
