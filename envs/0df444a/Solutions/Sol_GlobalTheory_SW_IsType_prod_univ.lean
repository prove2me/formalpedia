-- Prove2me | solution 1 for GlobalTheory.SW.IsType.prod_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:09.425246+00:00
-- url     : https://prove2.me/submissions/2a5f773d-c018-494d-a9fa-a5baf6035b2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent

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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
namespace IsType
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {M : Type} [CommMonoid M] (g : (E →+* ℂ) → M) :
    ∏ σ, g σ = ∏ τ : Ψ, (g τ * g (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.prod_coe_sort Ψ (fun τ => g τ * g (ComplexEmbedding.conjugate τ)),
    Finset.prod_mul_distrib, ← Finset.prod_mul_prod_compl Ψ]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ; exact Finset.mem_compl.2 ((hΨ τ).1 hτ)
  · intro τ hτ
    by_contra hc
    exact Finset.mem_compl.1 hτ ((hΨ τ).2 hc)
  · intro τ _; exact star_star τ
  · intro τ _; exact star_star τ
  · intro τ _; rfl
end IsType
end GlobalTheory.SW
