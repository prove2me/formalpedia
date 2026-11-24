-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.segForm_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:20:21.813381+00:00
-- url     : https://prove2.me/submissions/651c6c74-3b7e-43cc-ad27-a5f975388861

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
theorem _root_.solution {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) {Gz : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ}
    (hG : Gz.IsHomogeneous n) (w : (Σ k, ι k) → ℕ) (hw : ∀ j, ∑ k, w ⟨k, E j k⟩ = 1) :
    IsWeightedHomogeneous w (segForm E Gz) n := by
  have hseg : ∀ j, IsWeightedHomogeneous w (∏ k, (X ⟨k, E j k⟩ : MRing ι)) 1 := fun j => by
    have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, E j k⟩ : MRing ι))
      (fun k => w ⟨k, E j k⟩) fun k _ => isWeightedHomogeneous_X _ w _
    rwa [hw j] at h
  rw [segForm, aeval_def, eval₂_eq']
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hdeg : ∑ j, m j = n := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hG (mem_support_iff.1 hm)
  have h1 : IsWeightedHomogeneous w (∏ j, (∏ k, (X ⟨k, E j k⟩ : MRing ι)) ^ m j) (∑ j, m j • 1) :=
    IsWeightedHomogeneous.prod _ _ _ fun j _ => (hseg j).pow _
  have h2 : (∑ j, m j • 1) = n := by simpa using hdeg
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w (coeff m Gz)).mul h1
  rw [zero_add] at h3
  convert h3 using 2
  exact RingHom.congr_fun (RingHom.ext_int _ _) _
end GlobalTheory.CompanionTheory.Ar.SegreChart
