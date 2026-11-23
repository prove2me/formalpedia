-- Prove2me | solution 1 for GlobalTheory.HostModel.finrank_rat_E21_eq_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:21.031967+00:00
-- url     : https://prove2.me/submissions/0cd74e4c-e407-4c1f-bba3-386426a0264c

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
theorem _root_.solution : Module.finrank ℚ E21 = 12 := by
  rw [IsCyclotomicExtension.finrank E21 (Polynomial.cyclotomic.irreducible_rat (n := 21) (by norm_num))]
  decide
end GlobalTheory.HostModel
