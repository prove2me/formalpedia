-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.weighted_abs_le_of_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:02:05.391254+00:00
-- url     : https://prove2.me/submissions/9a1ad589-e73f-4e0e-9bbf-1873dcb2eb3f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/FiniteCoupling.lean:L22-L42
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.weighted_abs_le_of_second_moment. The node keeps its source
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

/-- Weighted Cauchy--Schwarz bounds the first absolute moment by a bound on
the second moment. Zero weights are allowed. -/
theorem weighted_abs_le_of_second_moment (w f : Ω → ℝ) (σ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hσ : 0 ≤ σ)
    (hsecond : ∑ i, w i * (f i) ^ 2 ≤ σ ^ 2) :
    ∑ i, w i * |f i| ≤ σ := by
  have hcs : (∑ i, w i * |f i|) ^ 2 ≤
      (∑ i, w i) * ∑ i, w i * (f i) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _
      exact hw i
    · intro i _
      exact mul_nonneg (hw i) (sq_nonneg (f i))
    · intro i _
      apply le_of_eq
      rw [mul_pow, sq_abs]
      ring
  rw [hprob, one_mul] at hcs
  have hnonneg : 0 ≤ ∑ i, w i * |f i| :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg (f i)))
  nlinarith

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.weighted_abs_le_of_second_moment := @_root_.OAI.LeanBlast.GotsmanLinial.weighted_abs_le_of_second_moment
