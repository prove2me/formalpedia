-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.NumericalMaximum.eventually_kissingNumber_lt_published
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/735dabfd-7863-4956-a1d2-76bc5407faae

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_kissing_spectral_certificate
import Theorems.Thm_MetricCodes_Numerics_kissing_entropy_certificate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_kissing_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_kissing_spectral_certificate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_kissing_entropy_certificate
import Theorems.Thm_MetricCodes_exists_maximal_sphericalCode
import Theorems.Thm_SpherePacking_exists_maximal_sphericalCode
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_main_general

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter Topology
open scoped Topology
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.NumericalMaximum
namespace MetricCodes.Spherical.HigherHierarchy.NumericalMaximum
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.kissingNumber n).toNat : ℝ) ≤
        (2 : ℝ) ^ ((0.39661 : ℝ) * (n : ℝ)) := by
  have hcode :=
    (MetricCodes.Spherical.HigherHierarchy.main_general
      (s := (1 : ℝ) / 2) (by norm_num) (by norm_num)).1
      (R := (0.39661 : ℝ))
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissingAmbient
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissingStabilizer
      MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_interlacing
      (by linarith [MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_spectral_certificate])
      (by linarith [MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_entropy_certificate])
  filter_upwards [hcode] with n hn
  obtain ⟨C, hC⟩ :=
    SpherePacking.exists_maximal_sphericalCode (n := n) (s := (1 : ℝ) / 2)
      (by norm_num)
  have hcard : (SpherePacking.kissingNumber n).toNat = C.points.card := by
    change (SpherePacking.sphericalCodeNumber n ((1 : ℝ) / 2)).toNat = _
    rw [← hC]
    exact ENat.toNat_coe _
  rw [hcard]
  exact (hn C).le
end MetricCodes.Spherical.HigherHierarchy.NumericalMaximum
