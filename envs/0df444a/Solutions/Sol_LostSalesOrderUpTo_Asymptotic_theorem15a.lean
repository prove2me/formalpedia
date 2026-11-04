-- Prove2me | solution 1 for LostSalesOrderUpTo.Asymptotic.theorem15a
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:29:11.912727+00:00
-- url     : https://prove2.me/submissions/a12d14a9-b51d-4ddc-87d0-930a0ce9bfd3

import Theorems.Thm_LostSalesOrderUpTo_Asymptotic_newsvendor_optimal
import Theorems.Thm_LostSalesOrderUpTo_Asymptotic_lemma13
import Theorems.Thm_LostSalesOrderUpTo_Asymptotic_jss_lower_bound

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

/-- Theorem 15(a), with the paper's exact finite-penalty factor. -/
theorem solution (P : CappedBaseStock.DemandLaw)
    (c : CappedBaseStock.Parameters)
    (hhold : 0 < expectedHolding (leadTimeLaw P c.L)
      (newsvendorLevel (leadTimeLaw P c.L) c.h
        (c.p / ((c.L : ℝ) + 1)))) :
    CappedBaseStock.baseStockCost P c
      (newsvendorLevel (leadTimeLaw P c.L) c.h
        (c.p + (c.L : ℝ) * c.h)) ≤
    ENNReal.ofReal
      ((1 + ((c.p + (c.L : ℝ) * c.h) * ((c.L : ℝ) + 1) / c.p) *
        shortageHoldingRatio (leadTimeLaw P c.L) c.h
          (c.p / ((c.L : ℝ) + 1))
          (newsvendorLevel (leadTimeLaw P c.L) c.h
            (c.p / ((c.L : ℝ) + 1)))) /
       (1 + shortageHoldingRatio (leadTimeLaw P c.L) c.h
          (c.p / ((c.L : ℝ) + 1))
          (newsvendorLevel (leadTimeLaw P c.L) c.h
            (c.p / ((c.L : ℝ) + 1))))) * CappedBaseStock.OPT P c := by
  let μ : Measure ℝ≥0 := leadTimeLaw P c.L
  let D : CappedBaseStock.DemandPath → ℝ≥0 :=
    fun d ↦ ∑ i ∈ Finset.range (c.L + 1), d i
  have hD : Measurable D := by
    dsimp only [D]
    fun_prop
  have : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure ((CappedBaseStock.demandPathLaw P).map D)
    exact Measure.isProbabilityMeasure_map hD.aemeasurable
  have hmean : Integrable (fun d : ℝ≥0 ↦ (d : ℝ)) μ := by
    change Integrable (fun d : ℝ≥0 ↦ (d : ℝ))
      ((CappedBaseStock.demandPathLaw P).map D)
    apply (integrable_map_measure (g := fun d : ℝ≥0 ↦ (d : ℝ))
      (by fun_prop) hD.aemeasurable).2
    change Integrable (fun d : CappedBaseStock.DemandPath ↦
      ((∑ i ∈ Finset.range (c.L + 1), d i : ℝ≥0) : ℝ))
      (CappedBaseStock.demandPathLaw P)
    simp only [NNReal.coe_sum]
    refine integrable_finsetSum _ (fun i _ ↦ ?_)
    have heval := measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P.law) i
    exact heval.integrable_comp_of_integrable P.finiteMean
  let b₀ : ℝ := c.p / ((c.L : ℝ) + 1)
  let b₁ : ℝ := c.p + (c.L : ℝ) * c.h
  let S₀ : ℝ≥0 := newsvendorLevel μ c.h b₀
  let S₁ : ℝ≥0 := newsvendorLevel μ c.h b₁
  let ν : ℝ := b₁ * ((c.L : ℝ) + 1) / c.p
  let ψ : ℝ := shortageHoldingRatio μ c.h b₀ S₀
  let F : ℝ := (1 + ν * ψ) / (1 + ψ)
  let A : ℝ := c.h * expectedHolding μ S₀
  have hL : 0 < (c.L : ℝ) + 1 := by positivity
  have hb₀ : 0 < b₀ := div_pos c.penalty_pos hL
  have hb₁ : 0 < b₁ := add_pos_of_pos_of_nonneg c.penalty_pos
    (mul_nonneg (Nat.cast_nonneg _) c.holding_pos.le)
  have hshort (S : ℝ≥0) : 0 ≤ expectedShortfall μ S :=
    integral_nonneg (fun _ ↦ le_max_right _ _)
  have hholding (S : ℝ≥0) : 0 ≤ expectedHolding μ S :=
    integral_nonneg (fun _ ↦ le_max_right _ _)
  have hcost (b : ℝ) (hb : 0 ≤ b) (S : ℝ≥0) : 0 ≤ backorderCost μ c.h b S :=
    add_nonneg (mul_nonneg c.holding_pos.le (hholding S))
      (mul_nonneg hb (hshort S))
  have hA : 0 < A := mul_pos c.holding_pos hhold
  have hψ : 0 ≤ ψ := div_nonneg (mul_nonneg hb₀.le (hshort S₀)) hA.le
  have hν : 0 ≤ ν := div_nonneg (mul_nonneg hb₁.le hL.le) c.penalty_pos.le
  have hF : 0 ≤ F := div_nonneg (add_nonneg zero_le_one (mul_nonneg hν hψ))
    (add_nonneg zero_le_one hψ)
  have hψden : 0 < 1 + ψ := add_pos_of_pos_of_nonneg zero_lt_one hψ
  have hscale : ν * b₀ = b₁ := by
    dsimp only [ν, b₀]
    field_simp [c.penalty_pos.ne', hL.ne'] <;> ring
  have hψA : ψ * A = b₀ * expectedShortfall μ S₀ := by
    dsimp only [ψ, shortageHoldingRatio, A]
    exact div_mul_cancel₀ _ hA.ne'
  have hcost₀ : backorderCost μ c.h b₀ S₀ = (1 + ψ) * A := by
    change A + b₀ * expectedShortfall μ S₀ = (1 + ψ) * A
    rw [← hψA]
    ring
  have hcost₁ : backorderCost μ c.h b₁ S₀ = (1 + ν * ψ) * A := by
    calc
      _ = A + ν * (b₀ * expectedShortfall μ S₀) := by
        change A + b₁ * expectedShortfall μ S₀ = _
        rw [← hscale]
        ring
      _ = (1 + ν * ψ) * A := by
        rw [← hψA]
        ring
  have hnormal : F * backorderCost μ c.h b₀ S₀ = backorderCost μ c.h b₁ S₀ := by
    rw [hcost₀, hcost₁]
    dsimp only [F]
    rw [← mul_assoc, div_mul_cancel₀ _ hψden.ne']
  have hmin₀ : backorderCost μ c.h b₀ S₀ = backorderOptimalCost μ c.h b₀ :=
    newsvendor_optimal μ c.h b₀ c.holding_pos hb₀ hmean
  have hmin₁ : backorderCost μ c.h b₁ S₁ = backorderOptimalCost μ c.h b₁ :=
    newsvendor_optimal μ c.h b₁ c.holding_pos hb₁ hmean
  have hopt_le : backorderOptimalCost μ c.h b₁ ≤ backorderCost μ c.h b₁ S₀ := by
    apply csInf_le
    · exact ⟨0, by rintro _ ⟨S, rfl⟩; exact hcost b₁ hb₁.le S⟩
    · exact ⟨S₀, rfl⟩
  have hlower : ENNReal.ofReal (backorderCost μ c.h b₀ S₀) ≤
      CappedBaseStock.OPT P c := by
    rw [hmin₀]
    exact jss_lower_bound P c
  change CappedBaseStock.baseStockCost P c S₁ ≤ ENNReal.ofReal F * CappedBaseStock.OPT P c
  calc
    _ ≤ ENNReal.ofReal (backorderCost μ c.h b₁ S₁) := (lemma13 P c S₁).2
    _ = ENNReal.ofReal (backorderOptimalCost μ c.h b₁) := congrArg ENNReal.ofReal hmin₁
    _ ≤ ENNReal.ofReal (backorderCost μ c.h b₁ S₀) := ENNReal.ofReal_le_ofReal hopt_le
    _ = ENNReal.ofReal (F * backorderCost μ c.h b₀ S₀) := congrArg ENNReal.ofReal hnormal.symm
    _ = ENNReal.ofReal F * ENNReal.ofReal (backorderCost μ c.h b₀ S₀) :=
      ENNReal.ofReal_mul hF
    _ ≤ ENNReal.ofReal F * CappedBaseStock.OPT P c := mul_le_mul_right hlower _
