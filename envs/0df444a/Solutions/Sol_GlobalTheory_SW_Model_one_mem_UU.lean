-- Prove2me | solution 1 for GlobalTheory.SW.Model.one_mem_UU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:53.190883+00:00
-- url     : https://prove2.me/submissions/52dc7ccd-07a5-47ad-8e4b-6fb25c82f083

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
theorem _root_.solution (N : ℕ) : (1 : M2 E N) ∈ UU E N := by
  change ccT _ * _ * _ = _
  have : ccT (1 : M2 E N) = 1 := by
    ext i j; by_cases h : i = j <;> simp [ccT, cc, Matrix.one_apply, h, eq_comm]
  rw [this]; simp
end GlobalTheory.SW.Model
