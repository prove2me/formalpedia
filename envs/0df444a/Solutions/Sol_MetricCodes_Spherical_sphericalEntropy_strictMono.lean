-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalEntropy_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/093f6639-c3b8-4404-b2b3-17912639588f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_hasDerivAt_sphericalEntropy

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution :
    StrictMonoOn MetricCodes.sphericalEntropy (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    sphericalEntropy_continuous.continuousOn
  intro u hu
  have hu' : 0 < u := by
    simpa only [interior_Ici, Set.mem_Ioi] using hu
  rw [(hasDerivAt_sphericalEntropy hu').deriv]
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  apply (lt_div_iff₀ hu').2
  linarith
end MetricCodes.Spherical
