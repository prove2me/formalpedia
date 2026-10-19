-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_fixedTail_choose_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/e554b173-7b05-4598-8d0d-c7469d2d0e62

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
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
    (k : ℕ → ℕ) (c : ℕ) {a : ℝ} (ha : 0 < a)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + c).choose (k n) : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hplus :
      Tendsto (fun n : ℕ => ((k n + c : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 a) := by
    have h := hk.add (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
    simpa [Nat.cast_add, add_div] using h
  have hlog :
      Tendsto
        (fun n : ℕ => (c : ℝ) *
          (Real.log ((k n + c : ℕ) : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
    simpa using (tendsto_log_linear_div ha hplus).const_mul (c : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hlog
  · apply Eventually.of_forall
    intro n
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.choose_pos (by omega : k n ≤ k n + c)))
    · exact Nat.cast_nonneg n
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hchoose :
        (k n + c).choose (k n) = (k n + c).choose c :=
      Nat.choose_symm_add
    have hbound :
        ((k n + c).choose (k n) : ℝ) ≤
          (((k n + c : ℕ) ^ c : ℕ) : ℝ) := by
      rw [hchoose]
      exact_mod_cast Nat.choose_le_pow (k n + c) c
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hpos : 0 < ((k n + c).choose (k n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : k n ≤ k n + c)
    calc
      Real.log (((k n + c).choose (k n) : ℝ)) ≤
          Real.log ((((k n + c : ℕ) ^ c : ℕ) : ℝ)) :=
        Real.log_le_log hpos hbound
      _ = (c : ℝ) * Real.log ((k n + c : ℕ) : ℝ) := by
        push_cast
        rw [Real.log_pow]
end MetricCodes.Spherical.HigherHierarchy.Weyl
