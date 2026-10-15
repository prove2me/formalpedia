-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.sum_choose_mul_index_sq_range
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:00:47.249619+00:00
-- url     : https://prove2.me/submissions/67f806b9-8f6b-490b-98b3-fcc35bc73c1d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/BinomialMoments.lean:L52-L72
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.sum_choose_mul_index_sq_range. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments

-- ---- from OAI.Combinatorics.GotsmanLinial.BinomialMoments ----
namespace OAI

/-!
Exact finite moments of the symmetric binomial weights. These identities provide
the grading multiplicities and the variance used in the finite coupling estimate.
No probabilistic assumptions or measures enter the statements.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- The real sum of one row of Pascal's triangle. -/
theorem sum_choose_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.sum_range_choose n

/-- Pascal recursion for an arbitrary real function of the binomial index. -/
theorem sum_choose_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) * f k) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f k) +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f (k + 1) :=
  Finset.sum_choose_succ_mul (fun k _ => f k) n

/-- The first raw binomial moment, with a formula valid at `n = 0`. -/
theorem sum_choose_mul_index_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) =
      (n : ℝ) * (2 : ℝ) ^ n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_choose_succ]
      simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [Finset.sum_add_distrib, ih, sum_choose_range]
      simp only [pow_succ]
      ring

/-- The second raw binomial moment, with a formula valid at `n = 0`. -/
theorem sum_choose_mul_index_sq_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 : ℝ) ^ n / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_choose_succ]
      have hshift :
          (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) =
            (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) +
              2 * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) +
              ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      rw [hshift, ih, sum_choose_mul_index_range, sum_choose_range]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.sum_choose_mul_index_sq_range := @_root_.OAI.LeanBlast.GotsmanLinial.sum_choose_mul_index_sq_range
