-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Giv.ResProj.mem_mcPts_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:00.580533+00:00
-- url     : https://prove2.me/submissions/3051f97d-42b2-4644-97f1-b865364da26e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
namespace GlobalTheory.CompanionTheory.Ar.Giv.ResProj
theorem _root_.solution {γ : MRing ι} {w : (Σ k, ι k) → ℂ} :
    w ∈ mcPts (Ideal.span {γ}) ↔ (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) ∧ evC w γ = 0 := by
  refine ⟨fun h => ⟨h.1, h.2 γ (Ideal.subset_span rfl)⟩, fun h => ⟨h.1, fun f hf => ?_⟩⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  have h2 : eval w (map (Int.castRingHom ℂ) γ) = 0 := h.2
  rw [map_mul, map_mul, h2, mul_zero]
end GlobalTheory.CompanionTheory.Ar.Giv.ResProj
