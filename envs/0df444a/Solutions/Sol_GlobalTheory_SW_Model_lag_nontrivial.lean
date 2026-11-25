-- Prove2me | solution 1 for GlobalTheory.SW.Model.lag_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:44.077223+00:00
-- url     : https://prove2.me/submissions/6941578f-8729-4f77-b156-14f0ce13541e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Theorems.Thm_GlobalTheory_SW_Model_J_mem_UU
import Theorems.Thm_GlobalTheory_SW_Model_one_mem_UU
import Theorems.Thm_GlobalTheory_SW_Base_J_mem_UU
import Theorems.Thm_GlobalTheory_SW_Base_one_mem_UU


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
theorem _root_.solution (N : ℕ) : Nontrivial (Lag E (N + 1)) := by
  refine ⟨⟨⟨_, 1, Base.one_mem_UU, rfl⟩, ⟨_, _, Base.J_mem_UU, rfl⟩, fun h => ?_⟩⟩
  have h1 : botSpan (1 : M2 E (N + 1)) = botSpan (Matrix.J (Fin (N + 1)) E) := congrArg Subtype.val h
  have h2 : (Matrix.J (Fin (N + 1)) E) (Sum.inr 0) ∈ botSpan (1 : M2 E (N + 1)) := by
    rw [h1]; exact Submodule.subset_span ⟨0, rfl⟩
  have h3 : botSpan (1 : M2 E (N + 1)) ≤ LinearMap.ker (LinearMap.proj (Sum.inl 0)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    simp [Matrix.one_apply]
  simpa [Matrix.J] using h3 h2
end GlobalTheory.SW.Model
