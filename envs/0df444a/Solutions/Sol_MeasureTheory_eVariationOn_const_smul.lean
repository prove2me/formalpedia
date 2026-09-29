-- Prove2me | solution 1 for MeasureTheory.eVariationOn_const_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:37:59.157349+00:00
-- url     : https://prove2.me/submissions/3ae588f5-749d-481e-83d0-792d18ec9295

import Mathlib

universe u v

theorem solution {α : Type u} [LinearOrder α] {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (f : α → E) (s : Set α) :
    eVariationOn (fun x => c • f x) s
      = ENNReal.ofReal |c| * eVariationOn f s := by
  unfold eVariationOn
  rw [ENNReal.mul_iSup]
  congr 1
  funext p
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : (‖c‖₊ : ENNReal) = ENNReal.ofReal |c| := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs]
  rw [edist_smul₀, ENNReal.smul_def, smul_eq_mul, hc]
