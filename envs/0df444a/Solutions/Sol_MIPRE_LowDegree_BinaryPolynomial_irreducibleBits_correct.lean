-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.irreducibleBits_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:47:49.567108+00:00
-- url     : https://prove2.me/submissions/d69071d5-0d01-41bf-840f-53d8ad8f5655

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryIrreducibleConstructor.lean (solution of MIPRE.LowDegree.BinaryPolynomial.irreducibleBits_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Theorems.Thm_MIPRE_LowDegree_BinaryDegreeFactors_degreeFactors_prod
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_fold_assemblyStep_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_natDegree_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_primePowerBits_correct
import Theorems.Thm_MIPRE_LowDegree_DegreeArithmetic_ascendingUnary_eq
import Theorems.Thm_MIPRE_LowDegree_DegreeArithmetic_rawPrimePower_correct

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

namespace MIPRE.LowDegree.DegreeArithmetic
noncomputable section
open Cost Cost.PolyTimeFun Polynomial
/-- The output is exactly the canonical prime-power component of the target degree. -/
theorem primePowerUnary_correct (n q : ℕ) :
    primePowerUnary (unary n) (unary q) = unary (q ^ n.factorization q) := by
  by_cases hq : q.Prime
  · simp only [primePowerUnary, length_unary, hq, ↓reduceIte]
    exact rawPrimePower_correct n q hq
  · simp [primePowerUnary, hq, Nat.factorization_eq_zero_of_not_prime n hq, unary]
end
end MIPRE.LowDegree.DegreeArithmetic

namespace MIPRE.LowDegree.BinaryDegreeFactors
section
/-- Distinct prime indices contribute coprime powers; all other indices contribute one. -/
theorem degreeFactors_pairwise (n : ℕ) : (degreeFactors n).Pairwise Nat.Coprime := by
  rw [degreeFactors, List.pairwise_ofFn]
  intro i j hij
  by_cases hi : (i : ℕ).Prime
  · by_cases hj : (j : ℕ).Prime
    · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hi hj).mpr
        (by exact ne_of_lt (show (i : ℕ) < (j : ℕ) from hij)))
    · simp [Nat.factorization_eq_zero_of_not_prime n hj]
  · simp [Nat.factorization_eq_zero_of_not_prime n hi]
end
end MIPRE.LowDegree.BinaryDegreeFactors

namespace MIPRE.LowDegree.DegreeArithmetic
noncomputable section
open Cost Cost.PolyTimeFun
/-- The executing decomposition agrees exactly with the mathematical prime-power factors. -/
theorem primePowerPairs_eq (n : ℕ) :
    primePowerPairs (unary n) = List.ofFn (fun i : Fin (n + 1) =>
      (unary (i : ℕ), unary ((i : ℕ) ^ n.factorization (i : ℕ)))) := by
  rw [primePowerPairs, ascendingUnary_eq, length_unary, List.map_ofFn]
  congr 1
  funext i
  dsimp only [Function.comp_def]
  rw [primePowerUnary_correct]
end
end MIPRE.LowDegree.DegreeArithmetic

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial DegreeArithmetic
/-- Degree one has the fixed irreducible polynomial `X`. -/
theorem polyOfBits_X : polyOfBits [false, true] = (X : (ZMod 2)[X]) := by
  simp only [polyOfBits_cons, show polyOfBits [] = 0 from rfl, ofBool,
    Bool.false_eq_true, ↓reduceIte, C_0, C_1, mul_zero, add_zero, mul_one, zero_add]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial DegreeArithmetic
/-- Dispatch correctness includes neutral entries outside the prime factorization support. -/
theorem primePowerBits_factorization_correct (n q : ℕ) :
    let a := primePowerBits (unary q) (unary (q ^ n.factorization q))
    a.getLastD false = true ∧ (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) ∧
      (polyOfBits a).natDegree = q ^ n.factorization q := by
  apply primePowerBits_correct
  by_cases hq : q.Prime
  · exact Or.inr hq
  · exact Or.inl (Nat.factorization_eq_zero_of_not_prime n hq)
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial DegreeArithmetic
/-- Every printed component polynomial is monic and irreducible. -/
theorem degreePolynomials_correct (n : ℕ) :
    ∀ a ∈ degreePolynomials (unary n), (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) := by
  intro a ha
  simp only [degreePolynomials, primePowerPairs_eq, List.map_ofFn] at ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact (primePowerBits_factorization_correct n i).2.1 |> fun hm =>
    ⟨hm, (primePowerBits_factorization_correct n i).2.2.1⟩
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial DegreeArithmetic
/-- The polynomial degrees are exactly the mathematical prime-power contribution list. -/
theorem degreePolynomials_degrees (n : ℕ) :
    (degreePolynomials (unary n)).map (fun a => (polyOfBits a).natDegree) =
      BinaryDegreeFactors.degreeFactors n := by
  simp only [degreePolynomials, primePowerPairs_eq, List.map_ofFn, BinaryDegreeFactors.degreeFactors]
  congr 1
  funext i
  exact (primePowerBits_factorization_correct n i).2.2.2
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Cost.PolyTimeFun Polynomial DegreeArithmetic
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    (polyOfBits (irreducibleBits (unary n))).Monic ∧
      Irreducible (polyOfBits (irreducibleBits (unary n))) ∧
      (polyOfBits (irreducibleBits (unary n))).natDegree = n := by
  have hpos : 0 < n := hn
  let l := degreePolynomials (unary n)
  have hl : ∀ a ∈ l, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) := degreePolynomials_correct n
  have hprod : (l.map (fun a => (polyOfBits a).natDegree)).prod = n := by
    rw [degreePolynomials_degrees]
    exact BinaryDegreeFactors.degreeFactors_prod n hpos
  have hpair : l.Pairwise (fun a b => (polyOfBits a).natDegree.Coprime (polyOfBits b).natDegree) := by
    have hp := BinaryDegreeFactors.degreeFactors_pairwise n
    rw [← degreePolynomials_degrees n] at hp
    simpa only [List.pairwise_map] using hp
  have hfold := fold_assemblyStep_correct l (unary n) [false]
    (by simpa only [List.cons_append, List.nil_append, polyOfBits_X] using irreducible_X (R := ZMod 2))
    hl hpair (by intro a _; simp) (by simp only [List.length_singleton, one_mul, hprod, length_unary, le_refl])
  have hempty : (unary n).isEmpty = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have hz := List.isEmpty_iff_length_eq_zero.mp he
    rw [length_unary] at hz
    omega
  simp only [irreducibleBits, hempty, Bool.false_eq_true, if_false]
  refine ⟨monic_polyOfBits_append_true _, hfold.1, ?_⟩
  rw [natDegree_polyOfBits_append_true, hfold.2, List.length_singleton, one_mul, hprod]
end MIPRE.LowDegree.BinaryPolynomial
