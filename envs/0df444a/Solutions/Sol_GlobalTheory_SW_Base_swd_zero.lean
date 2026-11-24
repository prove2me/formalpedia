-- Prove2me | solution 1 for GlobalTheory.SW.Base.swd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:29.104235+00:00
-- url     : https://prove2.me/submissions/efb1dc2c-4df1-49a8-a598-8cd373215af9

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
theorem _root_.solution (M : ℕ) (φ : Fam E n N) (Z : CM Ψ N N) : swd Ψ M φ Z 0 0 = swDiff Ψ M φ Z := rfl
end GlobalTheory.SW.Base
