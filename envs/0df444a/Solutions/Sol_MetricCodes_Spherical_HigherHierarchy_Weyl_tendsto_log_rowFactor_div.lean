-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_rowFactor_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/22d0deb6-1b26-4307-86bc-8d15c067df77

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_fixedTail_choose_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_rowBinomial_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_linearRowFactor

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
    {r : ℕ} (i : Fin (r + 1))
    (lam : ℕ → Fin (r + 1) → ℕ) {a : ℝ} (ha : 0 < a)
    (hlamTop : Tendsto (fun n : ℕ => lam n i) atTop atTop)
    (hlam : Tendsto
      (fun n : ℕ => (lam n i : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ => Real.log (rowFactor n (lam n) i) / (n : ℝ))
      atTop
      (𝓝 ((1 + a) * Real.log (1 + a) - a * Real.log a)) := by
  have hlin := tendsto_linearRowFactor
    (fun n : ℕ => lam n i) (2 * (i.val + 1)) hlam
  have hlinlog :
      Tendsto
        (fun n : ℕ =>
          Real.log
            ((2 * (lam n i : ℝ) + (n : ℝ) -
                ((2 * (i.val + 1) : ℕ) : ℝ)) /
              ((n : ℝ) - ((2 * (i.val + 1) : ℕ) : ℝ))) /
            (n : ℝ))
        atTop (𝓝 0) := by
    have hlog := (Real.continuousAt_log
      (by positivity : 2 * a + 1 ≠ 0)).tendsto.comp hlin
    simpa [div_eq_mul_inv] using
      hlog.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbig := tendsto_log_rowBinomial_div i
    (fun n : ℕ => lam n i) ha hlamTop hlam
  have hsmall := tendsto_log_fixedTail_choose_div
    (fun n : ℕ => lam n i) (rowTail i) ha hlam
  have hsum := (hlinlog.add hbig).sub hsmall
  have heq :
      (fun n : ℕ =>
        (Real.log
            ((2 * (lam n i : ℝ) + (n : ℝ) -
                ((2 * (i.val + 1) : ℕ) : ℝ)) /
              ((n : ℝ) - ((2 * (i.val + 1) : ℕ) : ℝ))) /
            (n : ℝ) +
          Real.log
            (((lam n i + tailLength n r i).choose (lam n i) : ℝ)) /
              (n : ℝ)) -
          Real.log
            (((lam n i + rowTail i).choose (lam n i) : ℝ)) /
              (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (rowFactor n (lam n) i) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop (2 * r + 4)] with n hn
    rw [rowFactor_eq_binomial]
    have hlinpos :
        0 <
          (2 * (lam n i : ℝ) + (n : ℝ) -
              ((2 * (i.val + 1) : ℕ) : ℝ)) /
            ((n : ℝ) - ((2 * (i.val + 1) : ℕ) : ℝ)) := by
      have hden := linearDenominator_pos hn i
      apply div_pos
      · have hlam' : 0 ≤ (lam n i : ℝ) := Nat.cast_nonneg _
        push_cast
        push_cast at hden
        linarith
      · simpa using hden
    have hbigpos :
        0 < ((lam n i + tailLength n r i).choose (lam n i) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : lam n i ≤ lam n i + tailLength n r i)
    have hsmallpos :
        0 < ((lam n i + rowTail i).choose (lam n i) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : lam n i ≤ lam n i + rowTail i)
    push_cast at hlinpos
    push_cast
    rw [Real.log_mul hlinpos.ne' (div_ne_zero hbigpos.ne' hsmallpos.ne'),
      Real.log_div hbigpos.ne' hsmallpos.ne']
    ring
  simpa using hsum.congr' heq
end MetricCodes.Spherical.HigherHierarchy.Weyl
