-- Prove2me | solution 1 for KellyStochasticNetworks.CountableReversal.exponential_clocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:50:28.026807+00:00
-- url     : https://prove2.me/submissions/cd776b26-d001-454f-bcf5-1c95089763cd

import Mathlib

open MeasureTheory ProbabilityTheory

theorem g79x_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U) (r : ℝ) (hr : 0 < r) (hlaw : P.map U = expMeasure r) (x : ℝ) :
    P.real {ω | x < U ω} = 1 - cdf (expMeasure r) x := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h1 : P.real {ω | x < U ω} = (P.map U).real (Set.Ioi x) := by
    rw [map_measureReal_apply hU measurableSet_Ioi]; rfl
  rw [h1, hlaw, cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (hS : Measurable S) (lam : ℝ) (hlam : 0 < lam)
    (hSlaw : P.map S = expMeasure lam) :
    (∀ s t : ℝ, 0 < s → 0 < t →
      (P {ω | s + t < S ω}).toReal / (P {ω | t < S ω}).toReal =
        (P {ω | s < S ω}).toReal) ∧
    (∀ (T : Ω → ℝ) (μ : ℝ), Measurable T → 0 < μ →
      P.map T = expMeasure μ → IndepFun S T P →
      P.map (fun ω => min (S ω) (T ω)) = expMeasure (lam + μ)) := by
  constructor
  · intro s t hs ht
    have e := g79x_tail P S hS lam hlam hSlaw
    simp only [← measureReal_def]
    rw [e, e, e, cdf_expMeasure_eq hlam, cdf_expMeasure_eq hlam, cdf_expMeasure_eq hlam,
      if_pos (by linarith), if_pos ht.le, if_pos hs.le]
    simp only [sub_sub_cancel]
    rw [div_eq_iff (Real.exp_pos _).ne', ← Real.exp_add]; congr 1; ring
  · intro T μ hT hμ hTlaw hind
    have hm : Measurable (fun ω => min (S ω) (T ω)) := hS.min hT
    have : IsProbabilityMeasure (P.map (fun ω => min (S ω) (T ω))) :=
      Measure.isProbabilityMeasure_map hm.aemeasurable
    have : IsProbabilityMeasure (expMeasure (lam + μ)) := isProbabilityMeasure_expMeasure (by linarith)
    refine Measure.ext_of_Iic _ _ fun x => ?_
    rw [Measure.map_apply hm measurableSet_Iic]
    have hc : (fun ω => min (S ω) (T ω)) ⁻¹' Set.Iic x = (S ⁻¹' Set.Ioi x ∩ T ⁻¹' Set.Ioi x)ᶜ := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_Ioi, min_le_iff, not_and_or, not_lt]
    have hmeasI : MeasurableSet (S ⁻¹' Set.Ioi x ∩ T ⁻¹' Set.Ioi x) :=
      (hS measurableSet_Ioi).inter (hT measurableSet_Ioi)
    have hreal : P.real ((fun ω => min (S ω) (T ω)) ⁻¹' Set.Iic x) =
        1 - (1 - cdf (expMeasure lam) x) * (1 - cdf (expMeasure μ) x) := by
      rw [hc, probReal_compl_eq_one_sub hmeasI, measureReal_def,
        hind.measure_inter_preimage_eq_mul _ _ measurableSet_Ioi measurableSet_Ioi,
        ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]
      have e1 := g79x_tail P S hS lam hlam hSlaw x
      have e2 := g79x_tail P T hT μ hμ hTlaw x
      rw [← e1, ← e2]; rfl
    have hcdf : (expMeasure (lam + μ)).real (Set.Iic x) =
        1 - (1 - cdf (expMeasure lam) x) * (1 - cdf (expMeasure μ) x) := by
      rw [← cdf_eq_real, cdf_expMeasure_eq (by linarith), cdf_expMeasure_eq hlam, cdf_expMeasure_eq hμ]
      split_ifs
      · simp only [sub_sub_cancel]; rw [← Real.exp_add]; congr 2; ring
      · norm_num
    rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _),
      hreal, hcdf]
