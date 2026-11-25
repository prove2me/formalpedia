-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:29.36449+00:00
-- url     : https://prove2.me/submissions/e9783c64-2463-4398-abe3-769cc8c32ecd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_generator
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_gal_aeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution (L : FinExt l) : ∃ y ∈ L.1, ‖y‖ ≤ 1 ∧
    ∀ g : GQ l, g y = y → g ∈ L.1.fixingSubgroup := by
  haveI := L.2
  obtain ⟨x, hxL, hx, hgen⟩ := exists_generator L.1
  refine ⟨x, hxL, hx, fun g hg => (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_⟩
  have h1 : ∀ z ∈ L.1, ‖z‖ ≤ 1 → g z = z := fun z hz hn => by
    obtain ⟨p, rfl⟩ := hgen z hz hn
    rw [gal_aeval, hg]
  by_cases hn : ‖z‖ ≤ 1
  · exact h1 z hz hn
  · have := h1 z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_le.1 hn).le)
    rwa [map_inv₀, inv_inj] at this
end GlobalTheory.Cyc.DiffSmall
