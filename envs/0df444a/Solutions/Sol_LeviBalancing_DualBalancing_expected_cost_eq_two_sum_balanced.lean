-- Prove2me | solution 1 for LeviBalancing.DualBalancing.expected_cost_eq_two_sum_balanced
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:32:19.566659+00:00
-- url     : https://prove2.me/submissions/64f27f74-1e3b-42a2-a351-d0cc8dc8dcb6

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
import Definitions.Def_LeviBalancing_DualBalancing_Policy
open Finset MeasureTheory
open scoped ENNReal


namespace LeviBalancing.DualBalancing

lemma holding_nonneg_aux (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) (ht : 1 ≤ t) :
    0 ≤ marginalHolding I d Q t := by
  unfold marginalHolding
  apply sum_nonneg
  intro j hj
  rw [mem_Icc] at hj
  exact mul_nonneg (I.h_nonneg j (by omega) hj.2) (le_max_right _ _)

lemma backlog_nonneg_aux (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) (ht1 : 1 ≤ t)
    (ht2 : t ≤ (I.T : ℤ) - I.L) : 0 ≤ marginalBacklog I d Q t := by
  unfold marginalBacklog
  exact mul_nonneg (I.p_nonneg _ (by omega) (by omega)) (le_max_right _ _)

theorem cost_core {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℤ m} (I : Instance) (dem : DemandProcess ℱ μ I.T)
    (B : ℤ → Ω → ℝ) (hB : IsDualBalancing I ℱ μ dem.D B) :
    expectedCost I μ dem.D B =
      2 * ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
        ∫⁻ ω, ENNReal.ofReal ((μ[randHolding I dem.D B t | ℱ t]) ω) ∂μ := by
  set D := dem.D with hD
  -- key per-period facts
  have hH0 : ∀ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), ∀ ω, 0 ≤ randHolding I D B t ω := by
    intro t ht ω
    rw [mem_Icc] at ht
    exact holding_nonneg_aux I _ _ t ht.1
  have hP0 : ∀ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), ∀ ω, 0 ≤ randBacklog I D B t ω := by
    intro t ht ω
    rw [mem_Icc] at ht
    exact backlog_nonneg_aux I _ _ t ht.1 ht.2
  have key : ∀ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
      ∫⁻ ω, ENNReal.ofReal (randHolding I D B t ω) ∂μ =
        ∫⁻ ω, ENNReal.ofReal ((μ[randHolding I D B t | ℱ t]) ω) ∂μ ∧
      ∫⁻ ω, ENNReal.ofReal (randBacklog I D B t ω) ∂μ =
        ∫⁻ ω, ENNReal.ofReal ((μ[randHolding I D B t | ℱ t]) ω) ∂μ := by
    intro t ht
    have ht' := mem_Icc.mp ht
    have iH := hB.integrable_holding t ht'.1 ht'.2
    have iP := hB.integrable_backlog t ht'.1 ht'.2
    have hle : ℱ t ≤ m := ℱ.le t
    haveI : SigmaFinite (μ.trim hle) := inferInstance
    have cH : 0 ≤ᵐ[μ] μ[randHolding I D B t | ℱ t] :=
      condExp_nonneg (Filter.Eventually.of_forall (hH0 t ht))
    have cP : 0 ≤ᵐ[μ] μ[randBacklog I D B t | ℱ t] :=
      condExp_nonneg (Filter.Eventually.of_forall (hP0 t ht))
    have e1 : ∫⁻ ω, ENNReal.ofReal (randHolding I D B t ω) ∂μ =
        ENNReal.ofReal (∫ ω, randHolding I D B t ω ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal iH (Filter.Eventually.of_forall (hH0 t ht))).symm
    have e2 : ∫⁻ ω, ENNReal.ofReal (randBacklog I D B t ω) ∂μ =
        ENNReal.ofReal (∫ ω, randBacklog I D B t ω ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal iP (Filter.Eventually.of_forall (hP0 t ht))).symm
    have e3 : ∫⁻ ω, ENNReal.ofReal ((μ[randHolding I D B t | ℱ t]) ω) ∂μ =
        ENNReal.ofReal (∫ ω, (μ[randHolding I D B t | ℱ t]) ω ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal integrable_condExp cH).symm
    have i1 : ∫ ω, (μ[randHolding I D B t | ℱ t]) ω ∂μ = ∫ ω, randHolding I D B t ω ∂μ :=
      integral_condExp hle
    have i2 : ∫ ω, (μ[randBacklog I D B t | ℱ t]) ω ∂μ = ∫ ω, randBacklog I D B t ω ∂μ :=
      integral_condExp hle
    have i3 : ∫ ω, (μ[randHolding I D B t | ℱ t]) ω ∂μ =
        ∫ ω, (μ[randBacklog I D B t | ℱ t]) ω ∂μ :=
      integral_congr_ae (hB.balance t ht'.1 ht'.2)
    refine ⟨?_, ?_⟩
    · rw [e1, e3, i1]
    · rw [e2, e3]
      congr 1
      linarith
  unfold expectedCost marginalCost
  have hsum : ∀ ω, ENNReal.ofReal (∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
      (marginalHolding I (fun j => D j ω) (fun j => B j ω) t +
        marginalBacklog I (fun j => D j ω) (fun j => B j ω) t)) =
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
        (ENNReal.ofReal (randHolding I D B t ω) + ENNReal.ofReal (randBacklog I D B t ω)) := by
    intro ω
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply sum_congr rfl
      intro t ht
      exact ENNReal.ofReal_add (hH0 t ht ω) (hP0 t ht ω)
    · intro t ht
      exact add_nonneg (hH0 t ht ω) (hP0 t ht ω)
  simp_rw [hsum]
  rw [lintegral_finset_sum']
  · rw [mul_sum]
    apply sum_congr rfl
    intro t ht
    have ht' := mem_Icc.mp ht
    rw [lintegral_add_left' ((hB.integrable_holding t ht'.1 ht'.2).aemeasurable.ennreal_ofReal)]
    rw [(key t ht).1, (key t ht).2, two_mul]
  · intro t ht
    have ht' := mem_Icc.mp ht
    exact ((hB.integrable_holding t ht'.1 ht'.2).aemeasurable.ennreal_ofReal).add
      ((hB.integrable_backlog t ht'.1 ht'.2).aemeasurable.ennreal_ofReal)

end LeviBalancing.DualBalancing

open LeviBalancing.DualBalancing


theorem solution {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℤ m} (I : Instance) (dem : DemandProcess ℱ μ I.T)
    (B : ℤ → Ω → ℝ) (hB : IsDualBalancing I ℱ μ dem.D B) :
    expectedCost I μ dem.D B =
      2 * ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
        ∫⁻ ω, ENNReal.ofReal ((μ[randHolding I dem.D B t | ℱ t]) ω) ∂μ := by
  exact cost_core I dem B hB
