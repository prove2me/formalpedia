-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.seg_ratio_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:20:23.326711+00:00
-- url     : https://prove2.me/submissions/56963260-6f31-4581-a105-ecf586f6eebf

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
theorem _root_.solution [DecidableEq K] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c₀ : (k : K) → ι k)
    (hc : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (k : K) (i : ι k) :
    (∏ k', y ⟨k', Function.update c₀ k i k'⟩) / ∏ k', y ⟨k', c₀ k'⟩ = y ⟨k, i⟩ / y ⟨k, c₀ k⟩ := by
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    rw [Function.update_of_ne hb]
    exact div_self (hc b)
  · simp
end GlobalTheory.CompanionTheory.Ar.SegreChart
