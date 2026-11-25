-- Prove2me | solution 1 for GlobalTheory.SW.first_coordinate_admissible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:14:41.725645+00:00
-- url     : https://prove2.me/submissions/50946e5f-6b32-4eee-9cf1-51c2fec791b3

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
namespace GlobalTheory.SW
theorem _root_.solution : admitted 1 1 (0 : Fam E n N) :=
  ⟨⟨one_pos, one_pos⟩, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ h => (h rfl).elim,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
end GlobalTheory.SW
