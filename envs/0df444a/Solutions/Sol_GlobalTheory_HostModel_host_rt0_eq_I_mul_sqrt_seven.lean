-- Prove2me | solution 1 for GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:51.454802+00:00
-- url     : https://prove2.me/submissions/23cb0a7f-f049-434b-8ce2-f9e527b3e7d7

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
theorem _root_.solution : host.rt0 = Complex.I * (Real.sqrt 7 : ℝ) := rfl
end GlobalTheory.HostModel
