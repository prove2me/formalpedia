-- Prove2me | solution 1 for GlobalTheory.SW.Base.isType_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:17.470148+00:00
-- url     : https://prove2.me/submissions/23fb4b1a-de32-4277-a69d-d05f6f892b13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
namespace GlobalTheory.SW.Base
theorem _root_.solution {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : IsType X.Ψ := X.cmType
end GlobalTheory.SW.Base
