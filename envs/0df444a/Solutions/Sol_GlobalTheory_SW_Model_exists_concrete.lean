-- Prove2me | solution 1 for GlobalTheory.SW.Model.exists_concrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:14:37.660307+00:00
-- url     : https://prove2.me/submissions/35e5cfa3-75d6-4675-afeb-d7364adbe9cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Theorems.Thm_GlobalTheory_SW_Model_exists_isType

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution : ∃ (_ : IsCMField (CyclotomicField 3 ℚ))
    (Ψ : Finset (CyclotomicField 3 ℚ →+* ℂ)), IsType Ψ ∧ Ψ.Nonempty := by
  have : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have : IsCMField (CyclotomicField 3 ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (S := {3}) _ ⟨3, rfl, by norm_num⟩
  exact ⟨this, exists_isType⟩
end GlobalTheory.SW.Model
