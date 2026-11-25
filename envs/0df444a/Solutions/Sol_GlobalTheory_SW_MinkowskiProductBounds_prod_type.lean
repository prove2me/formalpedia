-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.prod_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:29.124193+00:00
-- url     : https://prove2.me/submissions/38a300fd-4f0a-4da3-a80e-5e2f455f0fe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution {M : Type} [CommMonoid M] (h : IsType Ψ) (f : (E →+* ℂ) → M) :
    ∏ σ, f σ = ∏ τ : Ψ, (f τ.1 * f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.prod_mul_distrib, Finset.prod_coe_sort Ψ f,
    Finset.prod_coe_sort Ψ fun τ => f (ComplexEmbedding.conjugate τ),
    ← Finset.prod_mul_prod_compl Ψ f]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa using (h a).1 ha
  · intro a ha
    have := h a
    simp only [Finset.mem_compl] at ha
    tauto
  · intro a _; exact star_star a
  · intro a _; exact star_star a
  · intro a _; rfl
end GlobalTheory.SW.MinkowskiProductBounds
