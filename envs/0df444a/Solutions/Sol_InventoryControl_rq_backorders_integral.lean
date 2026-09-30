-- Prove2me | solution 1 for InventoryControl.rq_backorders_integral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T18:08:19.982015+00:00
-- url     : https://prove2.me/submissions/d53519d2-32ba-40aa-8eb2-25b7044e7c8e

import Mathlib
import Definitions.Def_InventoryControl_rq

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (R Q m s : ℝ) (hQ : 0 < Q) (hs : 0 < s) :
    ∫ x, max (-x) 0 ∂(rqLevel R Q m s) = ∫ x in Set.Iic 0, rqCDF R Q m s x := by
  have hP : IsProbabilityMeasure (rqPosition R Q) := isProbabilityMeasure_rqPosition R Q hQ
  have : IsProbabilityMeasure (rqLevel R Q m s) := isProbabilityMeasure_rqLevel R Q m s hQ
  have h1 : Integrable (fun x : ℝ => x) (rqPosition R Q) := by
    unfold rqPosition ProbabilityTheory.cond
    refine Integrable.smul_measure ?_ ?_
    · exact continuous_id.integrableOn_Icc
    · simp [Real.volume_Icc, hQ]
  have h2 : Integrable (fun x : ℝ => x) (newsboyDemand m s) := by
    rw [newsboyDemand_eq]
    exact (memLp_id_gaussianReal 1).integrable le_rfl
  have hint : Integrable (fun x : ℝ => max (-x) 0) (rqLevel R Q m s) := by
    unfold rqLevel
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact ((h1.comp_fst (newsboyDemand m s)).sub (h2.comp_snd (rqPosition R Q))).neg.pos_part
  rw [hint.integral_eq_integral_meas_le (Filter.Eventually.of_forall fun x => le_max_right _ _)]
  have h0 : (Set.Iic (0:ℝ)) = Set.Iic (-0) := by simp
  rw [h0, ← integral_comp_neg_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : (0:ℝ) < t := ht
  simp only [rqCDF]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Iic, le_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h
    left
    linarith
