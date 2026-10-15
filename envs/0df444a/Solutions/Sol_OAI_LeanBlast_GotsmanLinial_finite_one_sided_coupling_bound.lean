-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.finite_one_sided_coupling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:03:23.340758+00:00
-- url     : https://prove2.me/submissions/5fd9601b-4c7e-4eae-9d57-a8815aa0ea2d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/FiniteCoupling.lean:L64-L123
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.finite_one_sided_coupling_bound. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_weighted_abs_eq_twice_positive_part
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_weighted_abs_le_of_second_moment

-- ---- from OAI.Combinatorics.GotsmanLinial.ScalarIncrements ----
namespace OAI

/-!
# Scalar inequalities for the one-sided coupling estimate

The increasing function `couplingPotential m t = (t-m)|t-m|/2` controls
squared distances from below and has a trapezoidal increment bound from above.
All arguments here are algebraic, by splitting according to the positions of
the endpoints relative to the center `m`.
-/

namespace LeanBlast.GotsmanLinial

theorem couplingPotential_increment_upper (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    couplingPotential m v - couplingPotential m u ≤
      (v - u) / 2 * (|u - m| + |v - m|) :=
  (couplingPotential_increment_bounds m huv).2

theorem monotone_couplingPotential (m : ℝ) : Monotone (couplingPotential m) := by
  intro u v huv
  have h := couplingPotential_increment_lower m huv
  nlinarith [sq_nonneg (v - u)]

theorem couplingPotential_sub_nonneg_iff (m u v : ℝ) :
    0 ≤ couplingPotential m v - couplingPotential m u ↔ u ≤ v := by
  rw [sub_nonneg, couplingPotential_le_iff]

theorem abs_couplingPotential_sub_of_le (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    |couplingPotential m v - couplingPotential m u| =
      couplingPotential m v - couplingPotential m u :=
  abs_of_nonneg ((couplingPotential_sub_nonneg_iff m u v).mpr huv)

/-- The pointwise lower bound in the coupling argument, without ordering the
two real variables. -/
theorem sq_sub_le_four_mul_abs_potential_sub (m u v : ℝ) :
    (u - v) ^ 2 ≤ 4 * |couplingPotential m u - couplingPotential m v| := by
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm, abs_couplingPotential_sub_of_le m huv]
    have h := couplingPotential_increment_lower m huv
    nlinarith
  · rw [abs_couplingPotential_sub_of_le m hvu]
    have h := couplingPotential_increment_lower m hvu
    nlinarith

/-- An upper bound for the positive part of a potential increment under a
one-sided bound on the original increment. -/
theorem max_couplingPotential_increment_le (m a u v : ℝ)
    (ha : 0 ≤ a) (hstep : v - u ≤ a) :
    max (couplingPotential m v - couplingPotential m u) 0 ≤
      a / 2 * (|u - m| + |v - m|) := by
  have hs : 0 ≤ |u - m| + |v - m| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  by_cases huv : u ≤ v
  · rw [max_eq_left ((couplingPotential_sub_nonneg_iff m u v).mpr huv)]
    have h := couplingPotential_increment_upper m huv
    have hp := mul_nonneg (sub_nonneg.mpr hstep) hs
    nlinarith
  · have hvu : v ≤ u := (not_le.mp huv).le
    rw [max_eq_right (sub_nonpos.mpr ((monotone_couplingPotential m) hvu))]
    nlinarith [mul_nonneg ha hs]

end LeanBlast.GotsmanLinial

end OAI

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

/-- The finite one-sided coupling lemma: identical marginals and an upper
bound `a` on `V - U` bound the mean square displacement by `8 * a * σ`.

The center `m` may be arbitrary. Taking it to be the common mean recovers the
variance bound with variance `σ²`; only the displayed second moment is used. -/
theorem finite_one_sided_coupling_bound (w U V : Ω → ℝ) (m σ a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hvariance : ∑ i, w i * (U i - m) ^ 2 = σ ^ 2)
    (hstep : ∀ i, w i ≠ 0 → V i - U i ≤ a) :
    ∑ i, w i * (U i - V i) ^ 2 ≤ 8 * a * σ := by
  let z : Ω → ℝ := fun i => couplingPotential m (V i) - couplingPotential m (U i)
  have hz : ∑ i, w i * z i = 0 := by
    simp only [z, mul_sub, Finset.sum_sub_distrib]
    rw [hsame (couplingPotential m), sub_self]
  have habs := weighted_abs_eq_twice_positive_part w z hz
  have hU : ∑ i, w i * |U i - m| ≤ σ :=
    weighted_abs_le_of_second_moment w (fun i => U i - m) σ hw hprob hσ hvariance.le
  have hV : ∑ i, w i * |V i - m| ≤ σ := by
    rw [← hsame (fun t => |t - m|)]
    exact hU
  have hpositive : ∑ i, w i * max (z i) 0 ≤ a * σ := by
    calc
      ∑ i, w i * max (z i) 0 ≤
          ∑ i, w i * (a / 2 * (|U i - m| + |V i - m|)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left
            (max_couplingPotential_increment_le m a (U i) (V i) ha (hstep i hi))
            (hw i)
      _ = a / 2 * ((∑ i, w i * |U i - m|) + ∑ i, w i * |V i - m|) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ a / 2 * (σ + σ) :=
        mul_le_mul_of_nonneg_left (add_le_add hU hV) (div_nonneg ha (by norm_num))
      _ = a * σ := by ring
  have hsquare : ∑ i, w i * (U i - V i) ^ 2 ≤ 4 * ∑ i, w i * |z i| := by
    calc
      ∑ i, w i * (U i - V i) ^ 2 ≤ ∑ i, w i * (4 * |z i|) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i)
        dsimp only [z]
        rw [abs_sub_comm]
        exact sq_sub_le_four_mul_abs_potential_sub m (U i) (V i)
      _ = 4 * ∑ i, w i * |z i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    ∑ i, w i * (U i - V i) ^ 2 ≤ 4 * ∑ i, w i * |z i| := hsquare
    _ = 8 * ∑ i, w i * max (z i) 0 := by rw [habs]; ring
    _ ≤ 8 * (a * σ) := mul_le_mul_of_nonneg_left hpositive (by norm_num)
    _ = 8 * a * σ := by ring

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.finite_one_sided_coupling_bound := @_root_.OAI.LeanBlast.GotsmanLinial.finite_one_sided_coupling_bound
