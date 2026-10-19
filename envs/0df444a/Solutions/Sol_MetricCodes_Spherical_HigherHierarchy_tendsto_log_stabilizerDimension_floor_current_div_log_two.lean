-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_log_stabilizerDimension_floor_current_div_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/782794ee-4962-4884-bcb5-2f8192eb3ba1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_nat_sequence_sub_cast_div
import Theorems.Thm_SpherePacking_tendsto_natCast_div_self
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_tendsto_log_dimension_div_log_two
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_flooredWeight_antitone
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_flooredCoordinates_succ_ratio

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} (b : Fin (r + 1) → ℝ)
    (hb : ∀ i, 0 < b i) (hanti : StrictAnti b) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (Weyl.dimension (n - 1) (Weyl.flooredWeight b n)) /
          (n : ℝ)) / Real.log 2)
      atTop (nhds (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (b i))) := by
  let lam : ℕ → Fin (r + 1) → ℕ :=
    fun n => Weyl.flooredWeight b (n + 1)
  have hbase := Weyl.tendsto_log_dimension_div_log_two lam b hb hanti
    (fun n => Weyl.flooredWeight_antitone hanti.antitone (n + 1))
    (fun i => by
      simpa [lam, Weyl.flooredWeight, Function.comp_def,
        Nat.cast_add, Nat.cast_one] using
        (tendsto_nat_floor_mul_atTop (b i) (hb i)).comp
          (tendsto_add_atTop_nat 1))
    (fun i => by
      simpa [lam, Weyl.flooredWeight, flooredCoordinates] using
        tendsto_flooredCoordinates_succ_ratio b i (hb i).le)
  have hshift := hbase.comp (tendsto_sub_atTop_nat 1)
  have hratio := SpherePacking.tendsto_nat_sequence_sub_cast_div
    (fun n : ℕ => n) 1 1 tendsto_id
      SpherePacking.tendsto_natCast_div_self
  have hproduct := hshift.mul hratio
  have heq :
      (fun n : ℕ =>
        ((Real.log (Weyl.dimension (n - 1) (lam (n - 1))) /
            ((n - 1 : ℕ) : ℝ)) / Real.log 2) *
          (((n - 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.log (Weyl.dimension (n - 1) (Weyl.flooredWeight b n)) /
          (n : ℝ)) / Real.log 2) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hpred : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show n - 1 ≠ 0 by omega)
    have hlog : Real.log 2 ≠ 0 :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have hindex : n - 1 + 1 = n := by omega
    simp only [lam, hindex]
    field_simp
  simpa using hproduct.congr' heq
end MetricCodes.Spherical.HigherHierarchy
