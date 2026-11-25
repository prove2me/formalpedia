-- Prove2me | solution 1 for GlobalTheory.closure_mem_irreducibleComponents_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:49.871826+00:00
-- url     : https://prove2.me/submissions/fc8c23e4-3b4e-417d-8696-d13058679dff

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{u}} {B : Type u}
    [CommRing B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (hq : q.asIdeal ∈ minimalPrimes B) : closure {j q} ∈ irreducibleComponents Y := by
  refine ⟨isIrreducible_singleton.closure, fun W hW hle ↦ ?_⟩
  have hη := hW.isGenericPoint_genericPoint_closure
  have h₁ : hW.genericPoint ⤳ j q := hη.specializes (subset_closure (hle (subset_closure rfl)))
  obtain ⟨q', hq'⟩ := h₁.mem_open j.isOpenEmbedding.isOpen_range ⟨q, rfl⟩
  rw [← hq'] at h₁ hη
  have h₂ : q'.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes q' q).mpr
    (j.isOpenEmbedding.isInducing.specializes_iff.mp h₁)
  obtain rfl : q' = q := PrimeSpectrum.ext (h₂.antisymm (hq.2 ⟨q'.isPrime, bot_le⟩ h₂))
  exact subset_closure.trans hη.def.ge
end GlobalTheory
