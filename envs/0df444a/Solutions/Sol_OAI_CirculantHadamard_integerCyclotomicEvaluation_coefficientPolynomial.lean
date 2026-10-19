-- Prove2me | solution 1 for OAI.CirculantHadamard.integerCyclotomicEvaluation_coefficientPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:53:26.279736+00:00
-- url     : https://prove2.me/submissions/2aff723b-4d40-413c-8e15-eef95b52a13a

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal

open OAI OAI.CirculantHadamard
universe uA
open Polynomial
open scoped BigOperators
theorem solution
    (A : Type uA) [CommRing A] (n : ℕ) [NeZero n] (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      AdjoinRoot.mk (cyclotomic n A)
        (DyadicRemainder.coefficientPolynomial n
          (fun i => algebraMap ℤ A (T.coeff (i : ZMod n)))) := by
  unfold integerCyclotomicEvaluation
  rw [CyclicRing.evaluate_apply]
  unfold DyadicRemainder.coefficientPolynomial
  rw [map_sum]
  symm
  apply Finset.sum_nbij' (fun i : ℕ => (i : ZMod n)) (fun a : ZMod n => a.val)
  · intro i _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.2 (ZMod.val_lt a)
  · intro i hi; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hi)
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro i hi
    have hv : ((i : ZMod n)).val = i := ZMod.val_cast_of_lt (Finset.mem_range.1 hi)
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
      AdjoinRoot.mk_C, CyclicPolynomial.powerCharacter_apply, hv]
    simp
