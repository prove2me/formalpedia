-- Prove2me | solution 1 for OAI.CirculantHadamard.DyadicRemainder.coefficientPolynomial_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:25.498084+00:00
-- url     : https://prove2.me/submissions/059afdaf-bda2-4c04-957b-f1323de3ab3e

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

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.DyadicRemainder
universe uR
open Polynomial Finset
variable {R : Type uR} [CommRing R]
theorem solution (m : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
      X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
  unfold coefficientPolynomial
  rw [two_mul, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [X_pow_mul_monomial, add_comm i m]; simp only [add_comm m i]
