-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPrimePowerTrace.flat_trace_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:15:55.293933+00:00
-- url     : https://prove2.me/submissions/3bb952d4-7f00-4663-8e6b-6f111e112202

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPrimePowerTrace.lean (solution of MIPRE.LowDegree.BinaryPrimePowerTrace.flat_trace_natDegree);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_flat_prime_power_root_pow_minpoly
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_irreducible_comp_prime_pow_of_nonresidue
import Theorems.Thm_MIPRE_LowDegree_BinaryPrimePowerTrace_traceElement_natDegree_of_root_degrees

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- The flat extension root has the full specified minimal polynomial. -/
theorem flat_prime_power_minpoly {F : Type*} [Field F]
    (f : Polynomial F) (hf : f.Monic) (hi : Irreducible f)
    (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f) :
    minpoly F (AdjoinRoot.root (f.comp (X ^ (q ^ e)))) = f.comp (X ^ (q ^ e)) := by
  have hm : (f.comp (X ^ (q ^ e))).Monic :=
    hf.comp (monic_X.pow _) (by simp [hq.ne_zero])
  let : Fact (Irreducible (f.comp (X ^ (q ^ e)))) :=
    ⟨irreducible_comp_prime_pow_of_nonresidue f hf hi q e hq hq2 hn⟩
  rw [AdjoinRoot.minpoly_root hm.ne_zero, hm.leadingCoeff, inv_one, C_1, mul_one]
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPrimePowerTrace
open Polynomial IntermediateField
theorem _root_.solution (f : (ZMod 2)[X]) (hf : f.Monic) (hi : Irreducible f)
    (q e : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f)
    (horder : orderOf (2 : ZMod q) = f.natDegree) (hcop : q.Coprime f.natDegree) :
    (minpoly (ZMod 2) (traceElement (AdjoinRoot.root (f.comp (X ^ (q ^ (e + 1)))))
      f.natDegree (q ^ (e + 1)))).natDegree = q ^ (e + 1) := by
  let F := f.comp (X ^ (q ^ (e + 1)))
  have hm : F.Monic := hf.comp (monic_X.pow _) (by simp [hq.ne_zero])
  let : Fact (Irreducible F) :=
    ⟨BinaryPolynomial.irreducible_comp_prime_pow_of_nonresidue f hf hi q (e + 1) hq hq2 hn⟩
  let : Fintype (AdjoinRoot F) := Fintype.ofEquiv (Fin F.natDegree → ZMod 2)
    (BinaryQuotient.coordinateEquiv F hm).symm.toEquiv
  let : Module.Finite (ZMod 2) (AdjoinRoot F) := hm.finite_adjoinRoot
  apply traceElement_natDegree_of_root_degrees (AdjoinRoot.root F) f.natDegree q e
    hi.natDegree_pos hq horder hcop (IntermediateField.adjoin_root_eq_top F)
  · rw [BinaryPolynomial.flat_prime_power_minpoly f hf hi q (e + 1) hq hq2 hn,
      natDegree_comp, natDegree_X_pow]
  · rw [BinaryPolynomial.flat_prime_power_root_pow_minpoly f hf hi q e hq hq2 hn,
      natDegree_comp, natDegree_X_pow]
end MIPRE.LowDegree.BinaryPrimePowerTrace
