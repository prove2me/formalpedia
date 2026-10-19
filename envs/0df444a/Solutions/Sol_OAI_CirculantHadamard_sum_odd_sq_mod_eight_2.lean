-- Prove2me | solution 2 for OAI.CirculantHadamard.sum_odd_sq_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:57:21.47418+00:00
-- url     : https://prove2.me/submissions/cdb7a739-0e32-4859-9c88-62b45415d441

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/ModEight.lean:L34-L49
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.sum_odd_sq_mod_eight. The node keeps its source
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ModEight ----
namespace OAI

universe uIota

/-!
# The odd-coefficient obstruction modulo eight

The identity coefficient of an integer cyclic norm is the sum of the actual
coefficient squares. Every odd square is one modulo eight. Consequently an
odd-coefficient element in a cyclic group of order divisible by eight cannot
have norm scalar `4 * u^2` with `u` odd. The divisibility hypothesis excludes
order four, so the explicit order-four example is not ruled out.
-/

namespace CirculantHadamard

open scoped BigOperators

/-- Every odd integer square is congruent to one modulo eight. -/
theorem odd_sq_mod_eight {a : ℤ} (ha : Odd a) :
    Int.ModEq 8 (a ^ 2) 1 := by
  rcases ha with ⟨k, rfl⟩
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
  rw [Int.modEq_iff_dvd]
  refine ⟨-m, ?_⟩
  nlinarith [hm]

/-- A finite sum of odd integer squares is congruent to the number of terms. -/
theorem sum_odd_sq_mod_eight {ι : Type uIota} (s : Finset ι) (a : ι → ℤ)
    (ha : ∀ i ∈ s, Odd (a i)) :
    Int.ModEq 8 (∑ i ∈ s, a i ^ 2) (s.card : ℤ) := by
  classical
  revert ha
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [Int.ModEq]
  · intro i s hi ih ha
    have hiOdd : Odd (a i) := ha i (Finset.mem_insert_self i s)
    have hsOdd : ∀ j ∈ s, Odd (a j) :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one, add_comm (s.card : ℤ) 1] using
      (odd_sq_mod_eight hiOdd).add (ih hsOdd)

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uIota} : type_of% @_root_.OAI.CirculantHadamard.sum_odd_sq_mod_eight.{uIota} := @_root_.OAI.CirculantHadamard.sum_odd_sq_mod_eight.{uIota}
