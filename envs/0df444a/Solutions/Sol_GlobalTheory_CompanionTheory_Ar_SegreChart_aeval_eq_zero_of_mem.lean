-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:29.006452+00:00
-- url     : https://prove2.me/submissions/d7868035-a52d-4ae2-8efc-027c3c686aec

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
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution {Ω : Type} [Field Ω] (v : (Σ k, ι k) → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal v) :
    aeval v f = 0 := by
  have h : mConeMap v f = 0 := hf
  have h2 := congrArg ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ) h
  rw [mConeMap, comp_aeval_apply, map_zero] at h2
  simpa using h2
end GlobalTheory.CompanionTheory.Ar.SegreChart
