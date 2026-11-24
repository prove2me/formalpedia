-- Prove2me | solution 1 for GlobalTheory.SiegelAction.block_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:11.795951+00:00
-- url     : https://prove2.me/submissions/cd57791f-3f42-45c8-b38b-9e8d3cd2907c

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
theorem _root_.solution {A B C D τ τ' : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hτ : τ.IsSymm) :
    (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) = τ - τ' := by
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 h
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by simpa using congrArg transpose h3
  have : (A * τ + B)ᵀ * (C * τ' + D) - (C * τ + D)ᵀ * (A * τ' + B) =
      τ * (Aᵀ * C - Cᵀ * A) * τ' + τ * (Aᵀ * D - Cᵀ * B) - (Dᵀ * A - Bᵀ * C) * τ' +
        (Bᵀ * D - Dᵀ * B) := by
    simp only [transpose_add, transpose_mul, hτ.eq]
    noncomm_ring
  rw [this, h1, h2, h3, h4]
  simp
end GlobalTheory.SiegelAction
