-- Prove2me | solution 2 for OAI.CirculantHadamard.integerCyclotomicEvaluation_coefficientPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:43:29.144234+00:00
-- url     : https://prove2.me/submissions/9fb14450-8db5-4197-a628-58ebad39795d

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/OrderCyclotomicDivisibility.lean:L28-L50
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.integerCyclotomicEvaluation_coefficientPolynomial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicIntegerEvaluation ----
namespace OAI

universe uA

/-!
# Integer cyclic evaluation and actual cyclotomic conjugation

The coefficient map is the integer cast into the cyclotomic quotient. The
character sends the cyclic generator to its adjoined root. The root-inverting
automorphism therefore carries evaluation to evaluation of the actual cyclic
group-ring involution.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]

theorem integerCyclotomicEvaluation_apply (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      ∑ a : ZMod n, (T.coeff a : AdjoinRoot (cyclotomic n A)) *
        AdjoinRoot.root (cyclotomic n A) ^ a.val := by
  rw [integerCyclotomicEvaluation, CyclicRing.evaluate_apply]
  rfl

variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderCyclotomicDivisibility ----
namespace OAI

universe uA

/-!
# Dyadic divisibility of opposite coefficient differences

We evaluate the actual integer cyclic group ring in the cyclotomic extension
of the integers localized at two. The norm identity forces divisibility in
that DVR. Its free monic presentation then transfers this divisibility to the
paired coefficient differences, and localization reflects it to the integers.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

/-- The canonical polynomial with the literal integer coefficients of a cyclic
element evaluates to the same element in the cyclotomic quotient. -/
theorem integerCyclotomicEvaluation_coefficientPolynomial
    (A : Type uA) [CommRing A] (n : ℕ) [NeZero n] (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      AdjoinRoot.mk (cyclotomic n A)
        (DyadicRemainder.coefficientPolynomial n
          (fun i => algebraMap ℤ A (T.coeff (i : ZMod n)))) := by
  classical
  rw [integerCyclotomicEvaluation_apply]
  simp only [DyadicRemainder.coefficientPolynomial, map_sum,
    ← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
    algebraMap_int_eq, Int.coe_castRingHom, map_intCast]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ a : Fin (n + 1), (T.coeff a : AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val) =
        ∑ a : Fin (n + 1), (T.coeff (Fin.ofNat (n + 1) a.val) :
          AdjoinRoot (cyclotomic (n + 1) A)) *
          AdjoinRoot.root (cyclotomic (n + 1) A) ^ a.val
      simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]

end CirculantHadamard

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open Polynomial
open scoped BigOperators


theorem solution.{uA} : type_of% @_root_.OAI.CirculantHadamard.integerCyclotomicEvaluation_coefficientPolynomial.{uA} := @_root_.OAI.CirculantHadamard.integerCyclotomicEvaluation_coefficientPolynomial.{uA}
