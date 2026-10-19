-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.componentFactors_prod
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:05.070373+00:00
-- url     : https://prove2.me/submissions/95cdf24d-731d-44c1-99f5-65423d4309ef

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFactors.lean (solution of MIPRE.LowDegree.BinaryQuotient.componentFactors_prod);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_componentFactor_isCoprime
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_componentFactor_prime

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
/-- Irreducibility follows from the primitive-component primality criterion. -/
theorem componentFactor_irreducible (f E : Polynomial (ZMod 2)) (hf : f ≠ 0)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    (he : PrimitiveBinaryComponent (AdjoinRoot.mk f E)) :
    Irreducible (componentFactor f E) :=
  (componentFactor_prime f E hf hsq he).irreducible
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
/-- Every nonzero quotient modulus has a monic supported gcd factor. -/
theorem componentFactor_monic (f E : Polynomial (ZMod 2)) (hf : f ≠ 0) :
    (componentFactor f E).Monic := by
  have hne : componentFactor f E ≠ 0 :=
    ne_zero_of_dvd_ne_zero hf (gcd_dvd_left f (E - 1))
  simpa only [componentFactor, normalize_gcd] using (Polynomial.monic_normalize hne)
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Polynomial
theorem _root_.solution (f : Polynomial (ZMod 2)) (hf : f.Monic)
    [Finite (AdjoinRoot f)]
    (hsq : Function.Bijective (fun x : AdjoinRoot f => x * x))
    {n : ℕ} (E : Fin n → Polynomial (ZMod 2))
    (he : ∀ i, PrimitiveBinaryComponent (AdjoinRoot.mk f (E i)))
    (horth : Pairwise (fun i j => AdjoinRoot.mk f (E i) * AdjoinRoot.mk f (E j) = 0))
    (hsum : ∑ i, AdjoinRoot.mk f (E i) = 1) :
    ∏ i, componentFactor f (E i) = f := by
  have hirr (i : Fin n) : Irreducible (componentFactor f (E i)) :=
    componentFactor_irreducible f (E i) hf.ne_zero hsq (he i)
  have hcop : Pairwise (fun i j => IsCoprime (componentFactor f (E i))
      (componentFactor f (E j))) := by
    intro i j hij
    exact componentFactor_isCoprime f (E i) (E j) (hirr i) (horth hij)
  have hdiv : (∏ i, componentFactor f (E i)) ∣ f :=
    Fintype.prod_dvd_of_coprime hcop (fun i => gcd_dvd_left f (E i - 1))
  have hzero (i : Fin n) : AdjoinRoot.mk f (E i) *
      AdjoinRoot.mk f (∏ j, componentFactor f (E j)) = 0 := by
    apply (componentFactor_dvd_iff f (E i) _ (he i).2.1).mp
    exact Finset.dvd_prod_of_mem (fun j => componentFactor f (E j)) (Finset.mem_univ i)
  have hz : (∑ i, AdjoinRoot.mk f (E i)) *
      AdjoinRoot.mk f (∏ j, componentFactor f (E j)) = 0 := by
    rw [Finset.sum_mul]
    simp only [hzero, Finset.sum_const_zero]
  rw [hsum, one_mul] at hz
  have hrev : f ∣ ∏ i, componentFactor f (E i) := AdjoinRoot.mk_eq_zero.mp hz
  have hmonic : (∏ i, componentFactor f (E i)).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => componentFactor_monic f (E i) hf.ne_zero)
  exact dvd_antisymm_of_normalize_eq hmonic.normalize_eq_self hf.normalize_eq_self hdiv hrev
end MIPRE.LowDegree.BinaryQuotient
