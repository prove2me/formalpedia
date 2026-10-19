-- Prove2me | solution 2 for OAI.CirculantHadamard.DyadicRemainder.coefficientPolynomial_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:31:28.080792+00:00
-- url     : https://prove2.me/submissions/5380cdc0-5e29-4468-890e-1a850309a725

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/DyadicRemainder.lean:L76-L92
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.DyadicRemainder.coefficientPolynomial_two_mul. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.DyadicRemainder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR

/-!
# Paired coefficients in a dyadic cyclotomic remainder

Reducing a polynomial of length `2 * m` modulo `X ^ m + 1` subtracts
the upper block of coefficients from the lower block. The construction
and the coefficient formulas work over every commutative ring.
-/

noncomputable section

namespace CirculantHadamard.DyadicRemainder

open Polynomial Finset

variable {R : Type uR} [CommRing R]

/-- Split the coefficient polynomial into its lower and upper blocks. -/
theorem coefficientPolynomial_two_mul (m : ℕ) (c : ℕ → R) :
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
      X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
  classical
  calc
    coefficientPolynomial (2 * m) c = coefficientPolynomial m c +
        ∑ i ∈ range m, monomial (m + i) (c (m + i)) := by
      rw [two_mul]
      exact sum_range_add (fun i => monomial i (c i)) m m
    _ = coefficientPolynomial m c +
        X ^ m * coefficientPolynomial m (fun i => c (i + m)) := by
      congr 1
      simp only [coefficientPolynomial, mul_sum, X_pow_mul_monomial]
      apply sum_congr rfl
      intro i _
      rw [Nat.add_comm m i]

end CirculantHadamard.DyadicRemainder

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.DyadicRemainder
open Polynomial Finset


theorem solution.{uR} : type_of% @_root_.OAI.CirculantHadamard.DyadicRemainder.coefficientPolynomial_two_mul.{uR} := @_root_.OAI.CirculantHadamard.DyadicRemainder.coefficientPolynomial_two_mul.{uR}
