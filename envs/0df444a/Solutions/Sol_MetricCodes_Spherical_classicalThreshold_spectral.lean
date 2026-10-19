-- Prove2me | solution 1 for MetricCodes.Spherical.classicalThreshold_spectral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/346e3eae-4649-4e73-9d0e-dbec0ca38053

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    2 * MetricCodes.Gamma (MetricCodes.classicalThreshold s) 0 = s := by
  have ha : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - s ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hrootsq := Real.sq_sqrt hrad.le
  have hidentity :
      4 * MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s) =
        s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 := by
    unfold MetricCodes.classicalThreshold
    field_simp [hroot.ne']
    nlinarith
  have hinner :
      0 < MetricCodes.classicalThreshold s *
        (1 + MetricCodes.classicalThreshold s) := by positivity
  have hinnersq := Real.sq_sqrt hinner.le
  have hlin : 0 < 1 + 2 * MetricCodes.classicalThreshold s := by positivity
  have htarget :
      2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s)) =
        s * (1 + 2 * MetricCodes.classicalThreshold s) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    calc
      (2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s))) ^ 2 =
          4 * MetricCodes.classicalThreshold s *
            (1 + MetricCodes.classicalThreshold s) := by
            rw [mul_pow, hinnersq]
            ring
      _ = s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 :=
        hidentity
      _ = (s * (1 + 2 * MetricCodes.classicalThreshold s)) ^ 2 := by
        ring
  rw [Gamma_zero ha, ← mul_div_assoc]
  exact (div_eq_iff hlin.ne').2 htarget
end MetricCodes.Spherical
