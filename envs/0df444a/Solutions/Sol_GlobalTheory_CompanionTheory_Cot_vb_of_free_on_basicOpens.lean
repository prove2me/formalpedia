-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:25:53.905463+00:00
-- url     : https://prove2.me/submissions/fb1317a4-dbb2-48e9-8ac9-3fa3b5930f99

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VectorBundleOfLocalFreeness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cot
namespace GlobalTheory.CompanionTheory.Cot
theorem _root_.solution :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ),
      (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
        Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by
  intro R W _ _ _ g h
  choose r hr hfree hfin hrank using h
  have hs : Ideal.span (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have hfp : Module.FinitePresentation R W := by
    refine Module.FinitePresentation.of_localizationSpan' (Set.range r) hs
      (Rₚ := fun x => Localization.Away x.1) (Mₚ := fun x => Localization.Away x.1 ⊗[R] W)
      (fun x => TensorProduct.mk R (Localization.Away x.1) W 1) (fun x => ?_)
    obtain ⟨x, p, rfl⟩ := x
    have := hfree p
    have := hfin p
    exact Module.finitePresentation_of_projective (Localization.Away (r p))
      (Localization.Away (r p) ⊗[R] W)
  have hproj : Module.Projective R W := by
    rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro p
    have hsub : (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R W := by
      rw [Module.basicOpen_subset_freeLocus_iff]
      have := hfree p
      exact Module.Projective.of_equiv
        (LocalizedModule.equivTensorProduct (Submonoid.powers (r p)) W).symm
    exact hsub (hr p)
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hfl := hfree p
  have hfi := hfin p
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (r p)) (r p)
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r p)))) := by
    rw [hrange]
    exact hr p
  obtain ⟨q', hq'⟩ := hp
  rw [← hq', ← Module.rankAtStalk_baseChange q', Module.rankAtStalk_eq_finrank_of_free]
  exact hrank p
end GlobalTheory.CompanionTheory.Cot
