-- Prove2me | solution 1 for OAI.CirculantHadamard.cyclotomicPowerCharacter_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:53:59.948735+00:00
-- url     : https://prove2.me/submissions/831b6e5f-b51a-4e9a-b530-f16205e11b37

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

open OAI OAI.CirculantHadamard
universe uA
open Polynomial
open scoped BigOperators
variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]
variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]
theorem solution (a : ZMod n) :
    CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
        (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd (-a)) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
          (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd a)) := by
  rw [CyclicPolynomial.powerCharacter_apply, CyclicPolynomial.powerCharacter_apply,
    map_pow, RamifiedConjugation.cyclotomicConjugation_root, ← pow_mul]
  have h := RamifiedConjugation.root_pow_order A n
  rw [pow_eq_pow_mod _ h, pow_eq_pow_mod ((n - 1) * a.val) h]
  congr 1
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
  simp
