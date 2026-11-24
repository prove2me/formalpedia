-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_segForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:27.136391+00:00
-- url     : https://prove2.me/submissions/c8716106-4e11-42d3-8c33-a00d1c8591e8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution {R : Type} [CommRing R] (v : (Σ k, ι k) → R) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (Gz : MvPolynomial (Fin (N + 1)) ℤ) :
    aeval v (segForm E Gz) = aeval (fun j => ∏ k, v ⟨k, E j k⟩) Gz := by
  rw [segForm, comp_aeval_apply]
  simp only [map_prod, aeval_X]
end GlobalTheory.CompanionTheory.Ar.SegreChart
