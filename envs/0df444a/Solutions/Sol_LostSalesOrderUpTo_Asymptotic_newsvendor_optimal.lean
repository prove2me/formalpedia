-- Prove2me | solution 1 for LostSalesOrderUpTo.Asymptotic.newsvendor_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:24:35.598889+00:00
-- url     : https://prove2.me/submissions/f449f99c-913c-4ea1-a4fb-ebbdbe4bf1a9

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Theorems.Thm_RiskFunctionals_AVaR_quantile_mem_argmax
import Theorems.Thm_ProbabilityTheory_nonempty_setOf_le_cdf

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

/-- The critical-fractile quantile minimizes the integrable backorder cost. -/
theorem solution (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b)
    (hmean : Integrable (fun d : ℝ≥0 => (d : ℝ)) μ) :
    backorderCost μ h b (newsvendorLevel μ h b) =
      backorderOptimalCost μ h b := by
  let α : ℝ := b / (b + h)
  let Y : ℝ≥0 → ℝ := fun d ↦ (d : ℝ)
  have hY : Measurable Y := by fun_prop
  have hα₀ : 0 < α := div_pos hb (add_pos hb hh)
  have hα₁ : α < 1 := (div_lt_one (add_pos hb hh)).2 (by linarith)
  letI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hfin : ∃ u : ℝ, α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) u := by
    obtain ⟨u, hu⟩ := ProbabilityTheory.nonempty_setOf_le_cdf (μ.map Y) hα₁
    exact ⟨u, by simpa only [Set.mem_setOf_eq, ProbabilityTheory.cdf_eq_real,
      RiskFunctionals.AVaR.distributionFunction] using hu⟩
  have hdist (S : ℝ≥0) :
      RiskFunctionals.AVaR.distributionFunction (μ.map Y) (S : ℝ) =
        (distribution μ S).toReal := by
    rw [RiskFunctionals.AVaR.distributionFunction, measureReal_def,
      Measure.map_apply hY measurableSet_Iic]
    rfl
  have hnonneg (x : ℝ)
      (hx : α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) x) : 0 ≤ x := by
    by_contra hn
    have hxneg : x < 0 := lt_of_not_ge hn
    have hempty : Y ⁻¹' Set.Iic x = ∅ := by
      ext d
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_lt_of_le hxneg d.property)
    have hzero : RiskFunctionals.AVaR.distributionFunction (μ.map Y) x = 0 := by
      rw [RiskFunctionals.AVaR.distributionFunction, measureReal_def,
        Measure.map_apply hY measurableSet_Iic, hempty]
      simp
    rw [hzero] at hx
    exact (not_le_of_gt hα₀) hx
  have hset :
      ((↑) : ℝ≥0 → ℝ) '' {S : ℝ≥0 | ENNReal.ofReal α ≤ distribution μ S} =
        {x : ℝ | α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) x} := by
    ext x
    constructor
    · rintro ⟨S, hS, rfl⟩
      change α ≤ RiskFunctionals.AVaR.distributionFunction (μ.map Y) (S : ℝ)
      rw [hdist]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hS
    · intro hx
      let S : ℝ≥0 := ⟨x, hnonneg x hx⟩
      refine ⟨S, ?_, rfl⟩
      apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2
      change α ≤ (distribution μ S).toReal
      rw [← hdist S]
      exact hx
  have hquantile : (newsvendorLevel μ h b : ℝ) =
      RiskFunctionals.AVaR.quantileFunction (μ.map Y) α := by
    rw [newsvendorLevel, NNReal.coe_sInf]
    exact congrArg sInf hset
  have hopt := RiskFunctionals.AVaR.quantile_mem_argmax μ Y hY hmean α hα₀ hα₁.le hfin
  rw [← hquantile] at hopt
  simp only [← max_neg_neg, neg_sub, neg_zero] at hopt
  have hbalance (S : ℝ≥0) :
      expectedShortfall μ S = expectedHolding μ S + (∫ d : ℝ≥0, (d : ℝ) ∂μ) - (S : ℝ) := by
    have hp : Integrable (fun d : ℝ≥0 ↦ max ((d : ℝ) - (S : ℝ)) 0) μ :=
      (hmean.sub (integrable_const _)).pos_part
    have hm : Integrable (fun d : ℝ≥0 ↦ max ((S : ℝ) - (d : ℝ)) 0) μ :=
      ((integrable_const _).sub hmean).pos_part
    have hparts (d : ℝ≥0) :
        max ((d : ℝ) - (S : ℝ)) 0 - max ((S : ℝ) - (d : ℝ)) 0 = (d : ℝ) - (S : ℝ) := by
      simpa only [neg_sub] using max_zero_sub_max_neg_zero_eq_self ((d : ℝ) - (S : ℝ))
    have heq : expectedShortfall μ S - expectedHolding μ S =
        (∫ d : ℝ≥0, (d : ℝ) ∂μ) - (S : ℝ) := by
      unfold expectedShortfall expectedHolding
      rw [← integral_sub hp hm]
      simp_rw [hparts]
      rw [integral_sub hmean (integrable_const _)]
      simp
    linarith only [heq]
  have hcoeff : b * (1 / α) = b + h := by
    dsimp [α]
    field_simp [ne_of_gt hb]
  have hcost (S : ℝ≥0) : backorderCost μ h b S =
      b * (∫ d : ℝ≥0, (d : ℝ) ∂μ) -
        b * ((S : ℝ) - (1 / α) * expectedHolding μ S) := by
    rw [backorderCost, hbalance]
    calc
      _ = b * (∫ d : ℝ≥0, (d : ℝ) ∂μ) - b * (S : ℝ) +
          (b + h) * expectedHolding μ S := by ring
      _ = _ := by rw [← hcoeff]; ring
  have hmin (S : ℝ≥0) :
      backorderCost μ h b (newsvendorLevel μ h b) ≤ backorderCost μ h b S := by
    rw [hcost, hcost]
    apply sub_le_sub_left
    apply mul_le_mul_of_nonneg_left _ hb.le
    exact hopt (S : ℝ)
  have hleast : IsLeast (Set.range (backorderCost μ h b))
      (backorderCost μ h b (newsvendorLevel μ h b)) := by
    refine ⟨Set.mem_range_self _, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact hmin S
  exact hleast.csInf_eq.symm
