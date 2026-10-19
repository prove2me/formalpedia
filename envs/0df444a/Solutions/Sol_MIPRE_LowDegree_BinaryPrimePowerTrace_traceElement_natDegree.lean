-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:11:13.252074+00:00
-- url     : https://prove2.me/submissions/8797be15-62c7-41be-83d5-86f870b7b27b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryPrimePowerTrace.lean (solution of MIPRE.LowDegree.BinaryPrimePowerTrace.traceElement_natDegree);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_mem_range_iff_pow_card
import Theorems.Thm_MIPRE_LowDegree_BinaryPrimePowerTrace_traceElement_closed
import Theorems.Thm_MIPRE_LowDegree_BinaryPrimePowerTrace_traceElement_not_mem_range

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

namespace MIPRE.LowDegree.BinaryPrimePowerTrace
noncomputable section
open Polynomial IntermediateField
/-- The seed's multiplicative-order specification makes the reduced trace exponents distinct. -/
theorem exponent_residues_injective (m r q : ℕ) (horder : orderOf (2 : ZMod q) = m)
    (hcop : r.Coprime m) :
    Function.Injective (fun i : Fin m => 2 ^ (r * (i : ℕ)) % q) := by
  have hp : IsPrimitiveRoot (2 : ZMod q) m := IsPrimitiveRoot.iff_orderOf.mpr horder
  have hr := hp.pow_of_coprime r hcop
  intro i j hij
  apply Fin.ext
  apply hr.pow_inj i.isLt j.isLt
  rw [← pow_mul, ← pow_mul]
  have he := (ZMod.natCast_eq_natCast_iff' (2 ^ (r * (i : ℕ)))
    (2 ^ (r * (j : ℕ))) q).2 hij
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using he
end
end MIPRE.LowDegree.BinaryPrimePowerTrace

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPrimePowerTrace
open Polynomial IntermediateField
theorem _root_.solution {L E : Type*} [Field L] [Field E] [Finite L]
    [Algebra L E] [Algebra (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (β : E) (w : L) (m q e : ℕ) (hm : 0 < m) (hq : q.Prime)
    (hw : algebraMap L E w = β ^ q)
    (horder : orderOf (2 : ZMod q) = m) (hcop : q.Coprime m)
    (hcard : Nat.card L = 2 ^ (m * q ^ e))
    (hdeg : q ≤ (minpoly L β).natDegree)
    (hβ : β ^ (2 ^ (q ^ (e + 1) * m)) = β) :
    (minpoly (ZMod 2) (traceElement β m (q ^ (e + 1)))).natDegree = q ^ (e + 1) := by
  let : CharP E 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) E).injective 2
  let γ := traceElement β m (q ^ (e + 1))
  have hi : IsIntegral (ZMod 2) γ := IsIntegral.of_finite (ZMod 2) γ
  have hclosed : γ ^ (2 ^ (q ^ (e + 1))) = γ := traceElement_closed β m _ hβ
  have hdiv := (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius γ hi _).2 hclosed
  obtain ⟨j, hj, hd⟩ := (Nat.dvd_prime_pow hq).1 hdiv
  by_cases heq : j = e + 1
  · simpa [heq] using hd
  have hje : j ≤ e := by omega
  have hd' : (minpoly (ZMod 2) γ).natDegree ∣ q ^ e := by
    rw [hd]
    exact pow_dvd_pow q hje
  have hfix : iterateFrobenius E 2 (q ^ e) γ = γ :=
    (BinaryFiniteField.minpoly_natDegree_dvd_iff_frobenius γ hi _).1 hd'
  have hlarge : iterateFrobenius E 2 (q ^ e * m) γ = γ := by
    rw [iterateFrobenius_mul_apply]
    exact Function.IsFixedPt.iterate hfix m
  have hmem : γ ∈ (algebraMap L E).range := by
    apply (BinaryFiniteField.mem_range_iff_pow_card γ).2
    rw [hcard, Nat.mul_comm m]
    exact hlarge
  exact False.elim ((traceElement_not_mem_range β w m (q ^ (e + 1)) q hm hq.one_lt hw
    (exponent_residues_injective m _ q horder (hcop.pow_left _)) hdeg) hmem)
end MIPRE.LowDegree.BinaryPrimePowerTrace
