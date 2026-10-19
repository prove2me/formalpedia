-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.kissing_levelTwo_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/d250e08f-f26b-4e35-9712-fc6310a5e94e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_kissing_spectral_certificate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_kissing_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_kissing_spectral_certificate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    Interlacing Numerics.kissingAmbient Numerics.kissingStabilizer ∧
      (1 / 2 : ℝ) <
        2 * Gamma Numerics.kissingAmbient Numerics.kissingStabilizer := by
  refine ⟨Numerics.kissing_interlacing, ?_⟩
  linarith [Numerics.kissing_spectral_certificate]
end MetricCodes.Spherical.HigherHierarchy
