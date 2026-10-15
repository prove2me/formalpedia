-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.weighted_abs_eq_twice_positive_part
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:02:44.454596+00:00
-- url     : https://prove2.me/submissions/ff27c36d-6c35-417e-924e-cbbcde3e4eb4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/FiniteCoupling.lean:L44-L62
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.weighted_abs_eq_twice_positive_part. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements

-- ---- from OAI.Combinatorics.GotsmanLinial.FiniteCoupling ----
namespace OAI

/-!
# A finite one-sided coupling estimate

This is a finite weighted probabilistic estimate. Equal
marginals are expressed as equality of the weighted expectations of every
real function. The increment bound is required only on the support of the
nonnegative probability weights.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {Ω : Type*} [Fintype Ω]

/-- A weighted mean-zero variable has absolute first moment twice the first
moment of its positive part. This identity does not need positivity of the weights. -/
theorem weighted_abs_eq_twice_positive_part (w z : Ω → ℝ)
    (hzero : ∑ i, w i * z i = 0) :
    ∑ i, w i * |z i| = 2 * ∑ i, w i * max (z i) 0 := by
  calc
    ∑ i, w i * |z i| =
        (∑ i, w i * |z i|) + ∑ i, w i * z i := by rw [hzero, add_zero]
    _ = ∑ i, (w i * |z i| + w i * z i) := by rw [Finset.sum_add_distrib]
    _ = ∑ i, 2 * (w i * max (z i) 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 ≤ z i
      · rw [abs_of_nonneg hi, max_eq_left hi]
        ring
      · have hi' : z i ≤ 0 := (lt_of_not_ge hi).le
        rw [abs_of_nonpos hi', max_eq_right hi']
        ring
    _ = 2 * ∑ i, w i * max (z i) 0 := by rw [Finset.mul_sum]

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.weighted_abs_eq_twice_positive_part := @_root_.OAI.LeanBlast.GotsmanLinial.weighted_abs_eq_twice_positive_part
