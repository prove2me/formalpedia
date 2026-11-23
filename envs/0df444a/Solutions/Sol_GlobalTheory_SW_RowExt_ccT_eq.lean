-- Prove2me | solution 1 for GlobalTheory.SW.RowExt.ccT_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:47.77575+00:00
-- url     : https://prove2.me/submissions/5270d6b8-0809-4069-b0fe-706d382cbd3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.RowExt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}
namespace GlobalTheory.SW.RowExt
theorem _root_.solution (A : Matrix α β E) : ccT A = Aᴴ := rfl
end GlobalTheory.SW.RowExt
