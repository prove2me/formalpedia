-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.ideal_local_lower_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:01:58.424+00:00
-- url     : https://prove2.me/submissions/63c8cb9c-ee5c-461a-944e-b5e3fd5a0bda

import Mathlib
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_charge_bound_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem moment_integrable (n : ℕ) (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t^n*Real.exp (-t*x)) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem moment_nonneg (n : ℕ) (x : ℝ) : 0 ≤ moment n x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg (pow_nonneg ht.1 n) (Real.exp_pos _).le

theorem moment_le_one (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) : moment n x ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (moment_integrable n x) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1)
    (fun t (ht : t ∈ Icc (0:ℝ) 1) => show t^n*Real.exp (-t*x) ≤ (1:ℝ) from by
      have hpow : t^n ≤ 1 := pow_le_one₀ ht.1 ht.2
      have he : Real.exp (-t*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ht.1 hx0])
      exact (mul_le_of_le_one_left (Real.exp_pos _).le hpow).trans he)
  simpa only [moment, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

end MetricKMedian.Analytic
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_TimeAdvance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic
open Set

theorem abs_timeRate {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : |timeRate x y| ≤ 2 := by
  have hdiff : |y-x| ≤ 1 := abs_le.mpr ⟨by linarith only [hy0, hx1], by linarith only [hy1, hx0]⟩
  have hm0 := moment_nonneg 2 x
  have hm1 := moment_le_one 2 hx0
  rw [timeRate, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    abs_of_nonneg hx0, abs_of_nonneg hm0]
  have hprod : x*|y-x| ≤ 1 := (mul_le_of_le_one_left (abs_nonneg _) hx1).trans hdiff
  have h := mul_le_mul hprod hm1 hm0 (by norm_num : (0:ℝ) ≤ 1)
  nlinarith only [h]

end MetricKMedian.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_LocalForceScale
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

theorem ideal_local_lower_s35_oai (D : Actions I E) {x g b Q : ℝ}
    (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 < g) (hQ : 0 ≤ Q)
    (hd0 : ∀ i, 0 ≤ d i) (hdQ : ∀ i ∈ S, d i ≤ Q/g)
    (hy : mass g S ≤ 1) (hVQ : PhysicalPotential.cost g d S ≤ Q)
    (hb0 : 0 ≤ b) (hbQ : b ≤ 5*(Q/g)) :
    -(8*((relevant D S).card:ℝ)+2)*Q ≤
      timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant D S, charge D x g b d S e) := by
  have hc : ∀ e ∈ relevant D S, -(8*(Q/g)) ≤ charge D x g b d S e := by
    intro e _
    exact (abs_le.mp (charge_bound_s35 D d S hx0 hx1 hg.le (div_nonneg hQ hg.le)
      hd0 hdQ hy hb0 hbQ e)).1
  have hs := sum_le_sum hc
  simp only [sum_const, nsmul_eq_mul] at hs
  have hg' := mul_le_mul_of_nonneg_left hs hg.le
  have he : g*(((relevant D S).card:ℝ)* -(8*(Q/g)))=
      -(8*((relevant D S).card:ℝ)*Q) := by field_simp
  rw [he] at hg'
  have hr := (abs_le.mp (abs_timeRate hx0 hx1 (mass_nonneg hg.le S) hy)).1
  have hV0 : 0 ≤ PhysicalPotential.cost g d S := cost_nonneg hg.le (fun i _ => hd0 i)
  have ht := mul_le_mul_of_nonneg_right hr hV0
  nlinarith only [hg', ht, hVQ]

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedian.FixedBatch.ideal_local_lower_s35_oai.{u_1, u_2} := @OAI.MetricKMedian.FixedBatch.ideal_local_lower_s35_oai.{u_1, u_2}
