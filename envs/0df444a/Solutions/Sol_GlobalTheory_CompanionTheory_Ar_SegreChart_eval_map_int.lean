-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:34.303456+00:00
-- url     : https://prove2.me/submissions/bd3765a1-521c-44c9-a829-148750682ae8

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
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution {σ : Type} (v : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval v (map (Int.castRingHom ℂ) f) = aeval v f := by
  rw [aeval_def, eval₂_eq_eval_map]
  congr 2
end GlobalTheory.CompanionTheory.Ar.SegreChart
