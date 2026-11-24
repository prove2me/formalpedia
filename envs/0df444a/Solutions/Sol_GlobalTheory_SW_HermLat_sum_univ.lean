-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.sum_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:17.016812+00:00
-- url     : https://prove2.me/submissions/78e175ba-0284-4532-a6df-968e0fee3d49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HermLat
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (g : (E →+* ℂ) → ℂ) :
    ∑ σ, g σ = ∑ τ : Ψ, (g τ + g (ComplexEmbedding.conjugate τ.1)) := by
  rw [Finset.sum_coe_sort Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ)),
    Finset.sum_add_distrib, ← Finset.sum_add_sum_compl Ψ]
  congr 1
  symm
  refine Finset.sum_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ; exact Finset.mem_compl.2 ((hΨ τ).1 hτ)
  · intro τ hτ
    by_contra hc
    exact Finset.mem_compl.1 hτ ((hΨ τ).2 hc)
  · intro τ _; exact star_star τ
  · intro τ _; exact star_star τ
  · intro τ _; rfl
end GlobalTheory.SW.HermLat
