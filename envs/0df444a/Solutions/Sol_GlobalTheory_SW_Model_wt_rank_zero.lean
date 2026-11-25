-- Prove2me | solution 1 for GlobalTheory.SW.Model.wt_rank_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:48.087844+00:00
-- url     : https://prove2.me/submissions/75df2ee3-dae7-4969-a10a-109c8fd892f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Theorems.Thm_GlobalTheory_SW_Model_one_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_moves_one
import Theorems.Thm_GlobalTheory_SW_Base_one_mem_DH


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
theorem _root_.solution (M : ℕ) (Λ : Lt E 0) : wt M Λ = 1 := by
  have : {h ∈ DH E 0 M | Moves h Λ Λ} = {1} := by
    ext h
    obtain rfl : h = 1 := Subsingleton.elim _ _
    simp [one_mem_DH, Base.moves_one]
  simp [wt, this]
end GlobalTheory.SW.Model
