-- Prove2me | solution 1 for InventoryControl.rq_mean_level
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:11:17.039512+00:00
-- url     : https://prove2.me/submissions/527b382f-2e07-462e-bf3a-82c53e98cd81

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    ∫ x, x ∂(rqLevel R Q m s) = R + Q / 2 - m := by
  have hP : IsProbabilityMeasure (rqPosition R Q) := isProbabilityMeasure_rqPosition R Q hQ
  have h1 : Integrable (fun x : ℝ => x) (rqPosition R Q) := by
    unfold rqPosition ProbabilityTheory.cond
    refine Integrable.smul_measure ?_ ?_
    · exact continuous_id.integrableOn_Icc
    · simp [Real.volume_Icc, hQ]
  have h2 : Integrable (fun x : ℝ => x) (newsboyDemand m s) := by
    rw [newsboyDemand_eq]
    exact (memLp_id_gaussianReal 1).integrable le_rfl
  have hpos : ∫ x, x ∂(rqPosition R Q) = R + Q / 2 := by
    unfold rqPosition ProbabilityTheory.cond
    rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), integral_id]
    simp only [Real.volume_Icc, smul_eq_mul]
    rw [show R + Q - R = Q by ring, ENNReal.toReal_inv, ENNReal.toReal_ofReal hQ.le]
    field_simp
    ring
  have hdem : ∫ x, x ∂(newsboyDemand m s) = m := by
    rw [newsboyDemand_eq]
    exact integral_id_gaussianReal
  unfold rqLevel
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_sub (h1.comp_fst (newsboyDemand m s)) (h2.comp_snd (rqPosition R Q))]
  rw [integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x)]
  simp only [probReal_univ, one_smul, hpos, hdem]
