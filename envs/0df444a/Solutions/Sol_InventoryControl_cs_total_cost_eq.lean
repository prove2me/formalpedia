-- Prove2me | solution 1 for InventoryControl.cs_total_cost_eq
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T06:11:17.870094+00:00
-- url     : https://prove2.me/submissions/f39e94cb-c6b2-4d59-b022-209aeb9a72c6

import Definitions.Def_InventoryControl_clarkScarf

open MeasureTheory ProbabilityTheory

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace InventoryControl


lemma icAux_integrable_id (mu sigma : ℝ) (L : ℕ) :
    Integrable (fun x : ℝ => x) (csDemand mu sigma L) := by
  change Integrable id
    (gaussianReal (L * mu) (Real.toNNReal ((Real.sqrt L * sigma) ^ 2)))
  exact memLp_one_iff_integrable.mp
    (memLp_id_gaussianReal (μ := L * mu) (v := Real.toNNReal ((Real.sqrt L * sigma) ^ 2))
      (1 : NNReal))

lemma icAux_isProbabilityMeasure (mu sigma : ℝ) (L : ℕ) :
    IsProbabilityMeasure (csDemand mu sigma L) := by
  unfold csDemand
  infer_instance

lemma icAux_lipschitz_integral_max (D' : Measure ℝ) [IsProbabilityMeasure D']
    (hD' : Integrable (fun x : ℝ => x) D') :
    LipschitzWith 1 (fun y : ℝ => ∫ x, max (x - y) 0 ∂D') := by
  have hmax : ∀ y : ℝ, Integrable (fun x : ℝ => max (x - y) 0) D' := by
    intro y
    have h1 : Integrable (fun x : ℝ => x - y) D' := hD'.sub (integrable_const y)
    refine h1.norm.mono' (by fun_prop) ?_
    filter_upwards with x
    have := abs_max_sub_max_le_abs (x - y) 0 0
    simpa only [Real.norm_eq_abs, max_eq_left le_rfl, sub_zero] using this
  refine LipschitzWith.of_dist_le_mul fun y1 y2 => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  rw [← integral_sub (hmax y1) (hmax y2)]
  calc |∫ x, (max (x - y1) 0 - max (x - y2) 0) ∂D'|
      ≤ ∫ x, |max (x - y1) 0 - max (x - y2) 0| ∂D' := abs_integral_le_integral_abs
    _ ≤ ∫ x, |y1 - y2| ∂D' := by
        refine integral_mono ((hmax y1).sub (hmax y2)).abs (integrable_const _).abs ?_
        intro x
        have h2 : (x - y1) - (x - y2) = y2 - y1 := by ring
        have := abs_max_sub_max_le_abs (x - y1) (x - y2) 0
        simpa only [h2, abs_sub_comm] using this
    _ = |y1 - y2| := by
        rw [integral_const]
        simp

lemma icAux_integrable_comp_integral_max (D : Measure ℝ) [IsProbabilityMeasure D]
    (D' : Measure ℝ) (hD : Integrable (fun x : ℝ => x) D)
    (h_lip : LipschitzWith 1 (fun y : ℝ => ∫ x, max (x - y) 0 ∂D')) (y2 : ℝ) :
    Integrable (fun u : ℝ => ∫ x, max (x - (y2 - u)) 0 ∂D') D := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => ∫ x, max (x - (y2 - u)) 0 ∂D') D :=
    (h_lip.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hmoment : Integrable (fun u : ℝ => ‖u‖) D := hD.norm
  refine (Integrable.add (integrable_const (|∫ x, max (x - 0) 0 ∂D'| + |y2|)) hmoment).mono'
    hmeas ?_
  filter_upwards with u
  simp only [Pi.add_apply]
  have hdiff : |(∫ x, max (x - (y2 - u)) 0 ∂D') - (∫ x, max (x - 0) 0 ∂D')| ≤ |y2 - u| := by
    have := h_lip.dist_le_mul (y2 - u) 0
    rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, sub_zero] at this
  calc ‖∫ x, max (x - (y2 - u)) 0 ∂D'‖
      = |∫ x, max (x - (y2 - u)) 0 ∂D'| := Real.norm_eq_abs _
    _ ≤ |∫ x, max (x - (y2 - u)) 0 ∂D' - ∫ x, max (x - 0) 0 ∂D'|
          + |∫ x, max (x - 0) 0 ∂D'| := by
        have h : ‖∫ x, max (x - (y2 - u)) 0 ∂D'‖
            ≤ ‖∫ x, max (x - (y2 - u)) 0 ∂D' - ∫ x, max (x - 0) 0 ∂D'‖
              + ‖∫ x, max (x - 0) 0 ∂D'‖ := by
          calc ‖∫ x, max (x - (y2 - u)) 0 ∂D'‖
              = ‖(∫ x, max (x - (y2 - u)) 0 ∂D' - ∫ x, max (x - 0) 0 ∂D')
                  + ∫ x, max (x - 0) 0 ∂D'‖ := by rw [sub_add_cancel]
            _ ≤ ‖∫ x, max (x - (y2 - u)) 0 ∂D' - ∫ x, max (x - 0) 0 ∂D'‖
                  + ‖∫ x, max (x - 0) 0 ∂D'‖ := norm_add_le _ _
        simpa only [Real.norm_eq_abs] using h
    _ ≤ |y2 - u| + |∫ x, max (x - 0) 0 ∂D'| := by linarith
    _ ≤ (|y2| + ‖u‖) + |∫ x, max (x - 0) 0 ∂D'| := by
        have h2 : |y2 - u| ≤ |y2| + ‖u‖ := by
          calc |y2 - u| = |y2 + (-u)| := by ring_nf
            _ ≤ |y2| + |-u| := abs_add_le _ _
            _ = |y2| + ‖u‖ := by simp [Real.norm_eq_abs]
        linarith
    _ = |∫ x, max (x - 0) 0 ∂D'| + |y2| + ‖u‖ := by ring

lemma icAux_integrable_stage1_comp (e1 e2 b1 mu sigma : ℝ) (L1 L2 : ℕ) (y2 : ℝ) :
    Integrable (fun u : ℝ => csStage1Cost e1 e2 b1 mu sigma L1 (y2 - u))
      (csDemand mu sigma L2) := by
  haveI : IsProbabilityMeasure (csDemand mu sigma L2) := icAux_isProbabilityMeasure mu sigma L2
  haveI : IsProbabilityMeasure (csDemand mu sigma (L1 + 1)) :=
    icAux_isProbabilityMeasure mu sigma (L1 + 1)
  have hD : Integrable (fun x : ℝ => x) (csDemand mu sigma L2) := icAux_integrable_id mu sigma L2
  have hD' : Integrable (fun x : ℝ => x) (csDemand mu sigma (L1 + 1)) :=
    icAux_integrable_id mu sigma (L1 + 1)
  have h_lip := icAux_lipschitz_integral_max (csDemand mu sigma (L1 + 1)) hD'
  have hh : Integrable (fun u : ℝ => ∫ x, max (x - (y2 - u)) 0 ∂(csDemand mu sigma (L1 + 1)))
      (csDemand mu sigma L2) :=
    icAux_integrable_comp_integral_max (csDemand mu sigma L2) (csDemand mu sigma (L1 + 1))
      hD h_lip y2
  have hlin : Integrable (fun u : ℝ => e1 * (y2 - u) - (e1 + e2) * ((L1 + 1) * mu))
      (csDemand mu sigma L2) := by
    have h1 : Integrable (fun u : ℝ => e1 * (y2 - u)) (csDemand mu sigma L2) := by
      have h := (hD.const_mul (-e1)).add (integrable_const (e1 * y2))
      have hfun : ((fun x : ℝ => -e1 * x) + fun _ => e1 * y2) = fun u : ℝ => e1 * (y2 - u) := by
        funext u
        simp only [Pi.add_apply]
        ring
      rwa [hfun] at h
    exact h1.sub (integrable_const _)
  have hsum : Integrable (fun u : ℝ => e1 * (y2 - u) - (e1 + e2) * ((L1 + 1) * mu)
      + (e1 + e2 + b1) * ∫ x, max (x - (y2 - u)) 0 ∂(csDemand mu sigma (L1 + 1)))
      (csDemand mu sigma L2) := by
    have := hlin.add (hh.const_mul (e1 + e2 + b1))
    exact this
  simpa only [csStage1Cost] using hsum

end InventoryControl

open InventoryControl

theorem solution (e1 e2 b1 mu sigma : ℝ) (hs : 0 < sigma) (L1 L2 : ℕ) (S1 y2 : ℝ) :
    ∫ u, (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y2 - u)))
        ∂(csDemand mu sigma L2)
      = csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2 := by
  haveI : IsProbabilityMeasure (csDemand mu sigma L2) := icAux_isProbabilityMeasure mu sigma L2
  haveI : IsProbabilityMeasure (csDemand mu sigma (L1 + 1)) :=
    icAux_isProbabilityMeasure mu sigma (L1 + 1)
  have hg : Integrable (fun u : ℝ => csStage1Cost e1 e2 b1 mu sigma L1 (y2 - u))
      (csDemand mu sigma L2) := icAux_integrable_stage1_comp e1 e2 b1 mu sigma L1 L2 y2
  have hpt : ∀ u : ℝ, csStage2Cost e2 mu L2 y2
        + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y2 - u))
      = (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 S1)
        + Set.indicator (Set.Ioi (y2 - S1))
            (fun u : ℝ => csStage1Cost e1 e2 b1 mu sigma L1 (y2 - u)
              - csStage1Cost e1 e2 b1 mu sigma L1 S1) u := by
    intro u
    by_cases h : u ∈ Set.Ioi (y2 - S1)
    · have hlt : y2 - S1 < u := h
      have hm : min S1 (y2 - u) = y2 - u := min_eq_right (by linarith)
      rw [hm, Set.indicator_of_mem h]
      ring
    · have hle : u ≤ y2 - S1 := by
        have hnot : ¬ y2 - S1 < u := h
        linarith
      have hm : min S1 (y2 - u) = S1 := min_eq_left (by linarith)
      rw [hm, Set.indicator_of_notMem h]
      ring
  calc ∫ u, (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 (min S1 (y2 - u)))
        ∂(csDemand mu sigma L2)
      = ∫ u, ((csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 S1)
          + Set.indicator (Set.Ioi (y2 - S1))
              (fun u : ℝ => csStage1Cost e1 e2 b1 mu sigma L1 (y2 - u)
                - csStage1Cost e1 e2 b1 mu sigma L1 S1) u)
        ∂(csDemand mu sigma L2) :=
        integral_congr_ae (by filter_upwards with u; exact hpt u)
    _ = ∫ u, (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 S1)
          ∂(csDemand mu sigma L2)
        + ∫ u, Set.indicator (Set.Ioi (y2 - S1))
            (fun u : ℝ => csStage1Cost e1 e2 b1 mu sigma L1 (y2 - u)
              - csStage1Cost e1 e2 b1 mu sigma L1 S1) u
          ∂(csDemand mu sigma L2) :=
        integral_add (integrable_const _)
          ((hg.sub (integrable_const _)).indicator measurableSet_Ioi)
    _ = (csStage2Cost e2 mu L2 y2 + csStage1Cost e1 e2 b1 mu sigma L1 S1)
        + ∫ u in Set.Ioi (y2 - S1), (csStage1Cost e1 e2 b1 mu sigma L1 (y2 - u)
            - csStage1Cost e1 e2 b1 mu sigma L1 S1) ∂(csDemand mu sigma L2) := by
        rw [integral_const, integral_indicator measurableSet_Ioi]
        simp
    _ = csTotalCost e1 e2 b1 mu sigma L1 L2 S1 y2 := by
        simp only [csTotalCost]

