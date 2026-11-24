-- Prove2me | solution 1 for GlobalTheory.SW.Model.ccT_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:24.302017+00:00
-- url     : https://prove2.me/submissions/95c67f0d-8612-4fae-9ae7-9d398e781ebd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

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
theorem _root_.solution (N : ℕ) : ccT (Matrix.J (Fin N) E) = -Matrix.J (Fin N) E := by
  have : (Matrix.J (Fin N) E).map cc = Matrix.J (Fin N) E := by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [Matrix.J, cc, Matrix.one_apply, h]
  rw [ccT, this, Matrix.J_transpose]
end GlobalTheory.SW.Model
