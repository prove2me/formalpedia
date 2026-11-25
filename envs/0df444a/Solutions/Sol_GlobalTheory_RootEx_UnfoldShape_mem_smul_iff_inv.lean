-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.mem_smul_iff_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:22.811327+00:00
-- url     : https://prove2.me/submissions/b6081977-934f-430e-9117-565f3720801e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_mem_smul_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {ϖ : 𝒪[k]} (h : (ϖ : k) ≠ 0) {M : Submodule 𝒪[k] (ι → k)} {v : ι → k} :
    v ∈ ϖ • M ↔ (ϖ : k)⁻¹ • v ∈ M := by
  rw [mem_smul_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [inv_smul_smul₀ h]
  · intro hv
    exact ⟨_, hv, smul_inv_smul₀ h v⟩
end GlobalTheory.RootEx.UnfoldShape
