-- Prove2me | solution 1 for OAI.SharpPlanar.exp_segment_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:08:13.693959+00:00
-- url     : https://prove2.me/submissions/856d9a34-9055-41a2-8356-ed72538e2c8a

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma exp_segment_bound_e_oai {a l u : ℝ} (ha : 0 ≤ a) (hlu : l ≤ u) :
    (∫ t in l..u, Real.exp (-a*(u-t))) ≤ if a=0 then u-l else min (u-l) (1/a) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-a*(u-t))) := by fun_prop
  have hcl : (∫ t in l..u, Real.exp (-a*(u-t))) ≤ u-l := by
    calc
      _ ≤ ∫ t in l..u, (1:ℝ) := by
        apply intervalIntegral.integral_mono_on hlu (hc.intervalIntegrable l u) (continuous_const.intervalIntegrable l u)
        intro t ht
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sub_nonneg.mpr ht.2)
      _ = u-l := by simp
  split_ifs with h0
  · exact hcl
  · apply le_min hcl
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    have hp : ∀ t ∈ Set.uIcc l u, HasDerivAt (fun t : ℝ => Real.exp (-a*(u-t))/a)
        (Real.exp (-a*(u-t))) t := by
      intro t _
      exact ((((hasDerivAt_id t).const_sub u).const_mul (-a)).exp.div_const a).congr_deriv (by simp [h0])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hp (hc.intervalIntegrable l u)]
    simp only [sub_self,mul_zero,Real.exp_zero]
    exact sub_le_self _ (div_nonneg (Real.exp_pos _).le ha)

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.exp_segment_bound_e_oai := @OAI.SharpPlanar.exp_segment_bound_e_oai
