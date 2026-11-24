-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.evC_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:31.843366+00:00
-- url     : https://prove2.me/submissions/50f552d1-25ae-46d3-a42f-111a076def1f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_eval_map_int

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
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₂] [∀ k, Fintype (ι₂ k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (g : MRing ι) :
    evC z (rename (joinInl ι ι₂) g) = evC (fun p => z (joinInl ι ι₂ p)) g := by
  rw [evC, evC, eval_map_int, eval_map_int, aeval_rename]
  rfl
end GlobalTheory.CompanionTheory.Ar.SegreChart
