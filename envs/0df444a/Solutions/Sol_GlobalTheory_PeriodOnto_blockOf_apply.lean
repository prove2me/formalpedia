-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.blockOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:19.008747+00:00
-- url     : https://prove2.me/submissions/bac1bd9a-9953-4d17-8634-6c7ab418c1ac

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
variable {ι : Type} [Fintype ι] {g r : ℕ} (idx : Fin g ≃ ι × Fin r) (q : ℕ)
namespace GlobalTheory.PeriodOnto
theorem _root_.solution (t : ι) (z : Fin g → ℂ) (a : Fin r) :
    blockOf idx q t z a = kap q a (z (idx.symm (t, a))) := rfl
end GlobalTheory.PeriodOnto
