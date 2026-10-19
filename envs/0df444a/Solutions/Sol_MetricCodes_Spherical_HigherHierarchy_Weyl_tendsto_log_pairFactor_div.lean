-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_pairFactor_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/63b46fd5-a1f0-4b40-8dfa-8c9f5110f67b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_natCast_div_self
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_linear_div

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl
namespace MetricCodes.Spherical.HigherHierarchy.Weyl
theorem _root_.solution
    {r : ℕ} (i j : Fin (r + 1)) (hij : i < j)
    (lam : ℕ → Fin (r + 1) → ℕ)
    {aᵢ aⱼ : ℝ} (haᵢ : 0 < aᵢ) (haⱼ : 0 < aⱼ)
    (hsep : aⱼ < aᵢ)
    (hi : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 aᵢ))
    (hj : Tendsto (fun n : ℕ => (lam n j : ℝ) / (n : ℝ))
      atTop (𝓝 aⱼ)) :
    Tendsto (fun n : ℕ => Real.log (pairFactor n (lam n) i j) / (n : ℝ))
      atTop (𝓝 0) := by
  have hd : 0 < (j.val : ℝ) - (i.val : ℝ) := by
    have h : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  have hconst :=
    tendsto_const_div_atTop_nhds_zero_nat ((j.val : ℝ) - (i.val : ℝ))
  have hdiffscaled := ((hi.sub hj).add hconst).div_const
    ((j.val : ℝ) - (i.val : ℝ))
  simp only [add_zero] at hdiffscaled
  have hdiff :
      Tendsto
        (fun n : ℕ =>
          (((lam n i : ℝ) - (lam n j : ℝ) +
              (j.val : ℝ) - (i.val : ℝ)) /
            ((j.val : ℝ) - (i.val : ℝ))) / (n : ℝ))
        atTop
        (𝓝 ((aᵢ - aⱼ) / ((j.val : ℝ) - (i.val : ℝ)))) := by
    refine hdiffscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp; ring
  have hdiffLog := tendsto_log_linear_div
    (div_pos (sub_pos.mpr hsep) hd) hdiff
  have hone := SpherePacking.tendsto_natCast_div_self
  have hshift :=
    tendsto_const_div_atTop_nhds_zero_nat
      ((i.val : ℝ) + (j.val : ℝ) + 2)
  have hsumScaled := (((hi.add hj).add hone).sub hshift).div
    (hone.sub hshift) (by norm_num)
  simp only [sub_zero, div_one] at hsumScaled
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
              (i.val : ℝ) - (j.val : ℝ) - 2) /
            ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2))
        atTop (𝓝 (aᵢ + aⱼ + 1)) := by
    refine hsumScaled.congr' ?_
    filter_upwards [eventually_gt_atTop (i.val + j.val + 2)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (show 0 < n by omega)
    change
      (((lam n i : ℝ) / (n : ℝ) +
          (lam n j : ℝ) / (n : ℝ) + (n : ℝ) / (n : ℝ) -
          ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ)) /
        ((n : ℝ) / (n : ℝ) -
          ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ))) = _
    have hnum :
        (lam n i : ℝ) / (n : ℝ) +
            (lam n j : ℝ) / (n : ℝ) + (n : ℝ) / (n : ℝ) -
            ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ) =
          ((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
            ((i.val : ℝ) + (j.val : ℝ) + 2)) / (n : ℝ) := by
      ring
    have hden :
        (n : ℝ) / (n : ℝ) -
            ((i.val : ℝ) + (j.val : ℝ) + 2) / (n : ℝ) =
          ((n : ℝ) - ((i.val : ℝ) + (j.val : ℝ) + 2)) / (n : ℝ) := by
      ring
    rw [hnum, hden, div_div_div_cancel_right₀ hn']
    ring
  have hsumLog :
      Tendsto
        (fun n : ℕ =>
          Real.log
            (((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
                (i.val : ℝ) - (j.val : ℝ) - 2) /
              ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2)) /
            (n : ℝ))
        atTop (𝓝 0) := by
    have hlog := (Real.continuousAt_log
      (by positivity : aᵢ + aⱼ + 1 ≠ 0)).tendsto.comp hsum
    simpa [div_eq_mul_inv] using
      hlog.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htotal := hdiffLog.add hsumLog
  have heq :
      (fun n : ℕ =>
        Real.log
            (((lam n i : ℝ) - (lam n j : ℝ) +
                (j.val : ℝ) - (i.val : ℝ)) /
              ((j.val : ℝ) - (i.val : ℝ))) / (n : ℝ) +
          Real.log
            (((lam n i : ℝ) + (lam n j : ℝ) + (n : ℝ) -
                (i.val : ℝ) - (j.val : ℝ) - 2) /
              ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2)) /
            (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log (pairFactor n (lam n) i j) / (n : ℝ)) := by
    filter_upwards [
      hdiff.eventually (Ioi_mem_nhds
        (div_pos (sub_pos.mpr hsep) hd)),
      hsum.eventually (Ioi_mem_nhds
        (by positivity : 0 < aᵢ + aⱼ + 1)),
      eventually_gt_atTop (0 : ℕ)] with n hfirst hsecond hn
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfirst' :
        0 <
          ((lam n i : ℝ) - (lam n j : ℝ) +
              (j.val : ℝ) - (i.val : ℝ)) /
            ((j.val : ℝ) - (i.val : ℝ)) :=
      (div_pos_iff_of_pos_right hn').mp hfirst
    unfold pairFactor
    rw [Real.log_mul hfirst'.ne' hsecond.ne']
    ring
  simpa using htotal.congr' heq
end MetricCodes.Spherical.HigherHierarchy.Weyl
