-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.isMultiHomog_of_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:32.545223+00:00
-- url     : https://prove2.me/submissions/cb7d17b1-25d6-40d2-8f50-1b0393b4a54a

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
theorem _root_.solution [DecidableEq K] {s : MRing ι} {n : ℕ}
    (h : ∀ k, IsWeightedHomogeneous (fun p : Σ k, ι k => if p.1 = k then 1 else 0) s n) :
    IsMultiHomog s fun _ => n := by
  intro m hm k
  have h1 := h k (mem_support_iff.1 hm)
  rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp
end GlobalTheory.CompanionTheory.Ar.SegreChart
