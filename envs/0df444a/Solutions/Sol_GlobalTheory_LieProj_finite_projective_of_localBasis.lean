-- Prove2me | solution 1 for GlobalTheory.LieProj.finite_projective_of_localBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:42.843329+00:00
-- url     : https://prove2.me/submissions/26cc21fd-83cf-462d-8063-6d0a1778467b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteProjectiveOfLocalBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieProj
namespace GlobalTheory.LieProj
theorem _root_.solution : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    (∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (Module.Basis (Fin n) (Localization.Away r) (LocalizedModule (Submonoid.powers r) M))) →
    Module.Finite R M ∧ Module.Projective R M ∧ ∀ p, Module.rankAtStalk (R := R) M p = n := by
  intro R M _ _ _ n h
  let t : Set R := {r | Nonempty (Module.Basis (Fin n) (Localization.Away r)
    (LocalizedModule (Submonoid.powers r) M))}
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hb⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hle (Ideal.subset_span hb))
  have hfree : ∀ g : t, Module.Free (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
    fun g => Module.Free.of_basis g.2.some
  have hfp : ∀ g : t, Module.FinitePresentation (Localization.Away g.1)
      (LocalizedModule (Submonoid.powers g.1) M) := fun g => by
    haveI := hfree g
    haveI : Module.Finite (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
      Module.Finite.of_basis g.2.some
    exact Module.finitePresentation_of_projective _ _
  haveI : Module.FinitePresentation R M := Module.FinitePresentation.of_localizationSpan t ht hfp
  haveI : Module.Flat R M := by
    refine Module.flat_of_localized_span R M t ht ?_
    intro g
    haveI := hfree g
    haveI : Module.Flat R (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) _
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, fun p => ?_⟩
  obtain ⟨r, hr, ⟨b⟩⟩ := h p
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨q, rfl⟩ := hq
  haveI := Module.Free.of_basis b
  haveI : Nontrivial (Localization.Away r) := q.nontrivial
  rw [← Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers r) M) q,
    Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank (Localization.Away r) (LocalizedModule (Submonoid.powers r) M) = n
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
end GlobalTheory.LieProj
