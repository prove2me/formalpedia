-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.kap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:41.406159+00:00
-- url     : https://prove2.me/submissions/99416c64-1e19-42ec-8b38-2b2fda589cf9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (q a : ℕ) (c : ℂ) : kap q a c = if a < q then conj c else c := by
  unfold kap; split_ifs <;> simp
end GlobalTheory.PeriodOnto
