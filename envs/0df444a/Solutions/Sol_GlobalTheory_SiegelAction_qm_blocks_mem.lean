-- Prove2me | solution 1 for GlobalTheory.SiegelAction.qm_blocks_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:13.97121+00:00
-- url     : https://prove2.me/submissions/1cd885fb-4340-40eb-ba6d-e175a6d1bda5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (h : σ ∈ symplecticGroup ι ℚ) :
    fromBlocks (qm σ.toBlocks₁₁) (qm σ.toBlocks₁₂) (qm σ.toBlocks₂₁) (qm σ.toBlocks₂₂) ∈
      symplecticGroup ι ℂ := by
  have := SymplecticGroup.map_mem h (Rat.castHom ℂ)
  rw [← fromBlocks_toBlocks σ, fromBlocks_map] at this
  exact this
end GlobalTheory.SiegelAction
