-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.segForm_multiHomog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:37:02.893821+00:00
-- url     : https://prove2.me/submissions/f3ba41d1-a523-4b16-aa18-6e56a90f38f4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_isMultiHomog_of_weighted
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_segForm_weighted

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
theorem _root_.solution {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) {Gz : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ}
    (hG : Gz.IsHomogeneous n) : IsMultiHomog (segForm E Gz) fun _ => n := by
  classical
  exact isMultiHomog_of_weighted fun k => segForm_weighted E hG _ fun j => by simp
end GlobalTheory.CompanionTheory.Ar.SegreChart
