-- Prove2me | solution 1 for GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:51.368927+00:00
-- url     : https://prove2.me/submissions/bc1ecd22-78d5-40fa-8266-cf748d2fabc5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HostModel
theorem _root_.solution : host.w0 = halfSqrtNegSeven := rfl
end GlobalTheory.HostModel
