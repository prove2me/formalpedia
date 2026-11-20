-- Prove2me | solution 1 for InnerProductSpace.volume_closedBall_div_u0027__p2m_00b40815a546
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:12:58.023018+00:00
-- url     : https://prove2.me/submissions/28b3065e-8e5c-4750-98b2-c502fb33ab2d

import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F000


/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

@[expose] public section

open MeasureTheory WithLp

open scoped ENNReal NNReal ProbabilityTheory

                                     

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

end iIndepFun

section covariance

end covariance

end ProbabilityTheory

--generalizing `MeasureTheory.Measure.addHaar_ball_center`

open Metric

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) (r s : ℝ≥0∞) :
    volume (Metric.closedEBall x r) / volume (Metric.closedEBall y s) =
      (r / s) ^ (Module.finrank ℝ E) := by
  set n := Module.finrank ℝ E with hn
  set V := volume (Metric.closedBall (0 : E) 1) with hVdef
  have hV0 : V ≠ 0 := (Metric.measure_closedBall_pos volume (0 : E) one_pos).ne'
  have hVt : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have key : ∀ (z : E) (t : ℝ≥0∞), volume (Metric.closedEBall z t) = t ^ n * V := by
    intro z t
    induction t using ENNReal.recTopCoe with
    | top =>
      rw [Metric.closedEBall_top]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, pow_zero, one_mul, hVdef]
        have : ¬ Nontrivial E := fun h => by
          have := Module.finrank_pos_iff (R := ℝ) |>.mpr h
          omega
        haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp this
        congr 1
        ext w
        simp [Subsingleton.elim w 0]
      · rw [ENNReal.top_pow hpos.ne', ENNReal.top_mul hV0]
        haveI : Nontrivial E := Module.finrank_pos_iff (R := ℝ) |>.mp hpos
        exact measure_univ_of_isAddLeftInvariant volume
    | coe t =>
      rw [Metric.closedEBall_coe, Measure.addHaar_closedBall' volume z t.coe_nonneg,
        ENNReal.ofReal_pow t.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  rw [key, key, ENNReal.mul_div_mul_right _ _ hV0 hVt, div_eq_mul_inv, div_eq_mul_inv, mul_pow,
    ENNReal.inv_pow]
