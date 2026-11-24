-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.multiHomog_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:35:59.167498+00:00
-- url     : https://prove2.me/submissions/d87a182c-a6d5-4f83-af2b-742127c05d7e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_joinInl_inj

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
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog (rename (joinInl ι ι₂) g : MRing (joinIdx ι ι₂)) (Sum.elim d 0) := by
  classical
  intro m hm k
  rw [support_rename_of_injective joinInl_inj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases k with
  | inl k =>
    rw [Sum.elim_inl, ← hg m' hm' k]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply joinInl_inj m' ⟨k, i⟩
  | inr k =>
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨q, hq⟩
    exact Sum.inl_ne_inr (congrArg Sigma.fst hq)
end GlobalTheory.CompanionTheory.Ar.SegreChart
