-- Prove2me | solution 1 for MetricCodes.Numerics.packing_witness_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/df26f0f2-990b-4bb1-ab2b-21dea9b1e433

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution :
    0 < packingS ∧ packingS < 1 ∧ 0 < packingB ∧ packingB < packingA := by
  norm_num [packingS, packingA, packingB]
end MetricCodes.Numerics
