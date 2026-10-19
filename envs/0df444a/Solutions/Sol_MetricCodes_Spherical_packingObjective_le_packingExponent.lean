-- Prove2me | solution 1 for MetricCodes.Spherical.packingObjective_le_packingExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/0bdaa2b2-bf5b-4573-a27a-afe93b6a29cb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution {s a b : ℝ}
    (hs : 0 < s) (hs' : s < 1) (hf : Feasible s a b) :
    (packingObjective s a b : EReal) ≤ packingExponent := by
  exact le_sSup ⟨s, a, b, hs, hs', hf, rfl⟩
end MetricCodes.Spherical
