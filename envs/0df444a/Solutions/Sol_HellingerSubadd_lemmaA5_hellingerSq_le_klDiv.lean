-- Prove2me | solution 1 for HellingerSubadd.lemmaA5_hellingerSq_le_klDiv
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T08:59:51.608456+00:00
-- url     : https://prove2.me/submissions/0494371a-f69f-476d-8c17-6362ad4c7419

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory InformationTheory
open scoped ENNReal

namespace A5Aux

/-- Pointwise: `(√t - 1)² ≤ klFun t` for `t ≥ 0`. -/
lemma sq_sqrt_sub_one_le_klFun {t : ℝ} (ht : 0 ≤ t) : (Real.sqrt t - 1) ^ 2 ≤ klFun t := by
  set s := Real.sqrt t
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hts : t = s ^ 2 := (Real.sq_sqrt ht).symm
  have hk : 0 ≤ s * Real.log s + 1 - s := by
    have := klFun_nonneg hs0; rwa [klFun_apply] at this
  rw [klFun_apply, hts, Real.log_pow]
  push_cast
  nlinarith [mul_nonneg hs0 hk]

end A5Aux

theorem solution {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    HellingerSubadd.hellingerSq μ ν ≤ klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hac]; exact le_top
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hνξ : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  calc HellingerSubadd.hellingerSq μ ν
      ≤ ∫⁻ x, ν.rnDeriv (μ + ν) x *
          ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2) ∂(μ + ν) := by
        unfold HellingerSubadd.hellingerSq
        refine lintegral_mono_ae ?_
        filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ + ν) hac,
          Measure.rnDeriv_lt_top ν (μ + ν)] with x hx hq
        rw [← hx, Pi.mul_apply, ENNReal.toReal_mul]
        set r := μ.rnDeriv ν x
        set q := ν.rnDeriv (μ + ν) x
        have e : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hq.ne).symm
        refine le_of_eq ?_
        calc ENNReal.ofReal ((Real.sqrt (r.toReal * q.toReal) - Real.sqrt q.toReal) ^ 2)
            = ENNReal.ofReal q.toReal * ENNReal.ofReal ((Real.sqrt r.toReal - 1) ^ 2) := by
              rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
              congr 1
              rw [Real.sqrt_mul ENNReal.toReal_nonneg]
              rw [show q.toReal * (Real.sqrt r.toReal - 1) ^ 2
                  = (Real.sqrt q.toReal * (Real.sqrt r.toReal - 1)) ^ 2 by
                rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]]
              ring
          _ = q * ENNReal.ofReal ((Real.sqrt r.toReal - 1) ^ 2) := by rw [← e]
    _ = ∫⁻ x, ENNReal.ofReal ((Real.sqrt (μ.rnDeriv ν x).toReal - 1) ^ 2) ∂ν :=
        lintegral_rnDeriv_mul hνξ (by fun_prop)
    _ ≤ ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal
          (A5Aux.sq_sqrt_sub_one_le_klFun ENNReal.toReal_nonneg)
