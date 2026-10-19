-- Prove2me | solution 1 for MetricCodes.Numerics.kissing_witness_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/8536962f-1677-4e94-8841-a3af09693f85

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution : 0 < kissingB ∧ kissingB < kissingA := by
  constructor <;> norm_num [kissingA, kissingB]
end MetricCodes.Numerics
