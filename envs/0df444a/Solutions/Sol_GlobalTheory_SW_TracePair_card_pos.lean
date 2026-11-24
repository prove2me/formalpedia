-- Prove2me | solution 1 for GlobalTheory.SW.TracePair.card_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:28.968863+00:00
-- url     : https://prove2.me/submissions/141c1eca-12cf-4411-9411-204640a52ef5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TracePair
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SW.TracePair
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) : 0 < Ψ.card := by
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : σ ∈ Ψ
  · exact Finset.card_pos.2 ⟨σ, h⟩
  · refine Finset.card_pos.2 ⟨ComplexEmbedding.conjugate σ, ?_⟩
    by_contra h'
    exact h ((hΨ σ).2 h')
end GlobalTheory.SW.TracePair
