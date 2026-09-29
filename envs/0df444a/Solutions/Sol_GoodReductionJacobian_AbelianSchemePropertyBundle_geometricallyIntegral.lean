-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/72c70c72-8379-53ab-8149-2f5a354179f9

import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace S17A0

theorem isIntegral_of_smooth_of_connectedSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) [Smooth t] [ConnectedSpace X] : IsIntegral X := by
  haveI : LocallyOfFiniteType t := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  exact AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
    X fun x => by
      haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) x
      exact IsRegularLocalRing.isDomain _

scoped instance subsingleton_spec_field (K : Type u) [Field K] :
    Subsingleton ↥(Spec (CommRingCat.of K)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

scoped instance nonempty_spec_field (K : Type u) [Field K] :
    Nonempty ↥(Spec (CommRingCat.of K)) :=
  inferInstanceAs (Nonempty (PrimeSpectrum K))

section Stacks04KV

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
  (e : Spec (CommRingCat.of k) ⟶ A) (he : e ≫ f = 𝟙 _)

noncomputable abbrev bc (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

noncomputable def pt' : Spec (CommRingCat.of K) ⟶ pullback f (bc k K) :=
  pullback.lift (bc k K ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])

@[scoped simp] theorem pt'_fst : pt' f e he ≫ pullback.fst f (bc k K) = bc k K ≫ e := pullback.lift_fst _ _ _

include he in

theorem subsingleton_pullback_section :
    Subsingleton ↥(pullback e (pullback.fst f (bc k K))) := by

  let i₁ : pullback e (pullback.fst f (bc k K)) ≅ pullback (e ≫ f) (bc k K) :=
    pullbackRightPullbackFstIso f (bc k K) e
  let i₂ : pullback (e ≫ f) (bc k K) ≅ pullback (𝟙 _) (bc k K) := pullback.congrHom he rfl
  haveI : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of k))) (bc k K)) := inferInstance
  let j : pullback e (pullback.fst f (bc k K)) ⟶ Spec (CommRingCat.of K) :=
    i₁.hom ≫ i₂.hom ≫ pullback.snd (𝟙 _) (bc k K)
  haveI : IsIso j := by unfold j; infer_instance
  exact (Scheme.Hom.homeomorph j).subsingleton

theorem eq_pt'_of_fst_eq (v : ↥(pullback f (bc k K)))
    (hv : pullback.fst f (bc k K) v = e (IsLocalRing.closedPoint k)) :
    v = pt' f e he (IsLocalRing.closedPoint K) := by
  have hrange : Set.range (pullback.snd e (pullback.fst f (bc k K))) =
      pullback.fst f (bc k K) ⁻¹' Set.range e := Scheme.Pullback.range_snd _ _
  have hv' : v ∈ Set.range (pullback.snd e (pullback.fst f (bc k K))) := by
    rw [hrange]; exact ⟨_, hv.symm⟩
  have hp' : pt' f e he (IsLocalRing.closedPoint K) ∈
      Set.range (pullback.snd e (pullback.fst f (bc k K))) := by
    rw [hrange, Set.mem_preimage, ← Scheme.Hom.comp_apply, pt'_fst, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨z, rfl⟩ := hv'
  obtain ⟨z', hz'⟩ := hp'
  haveI := subsingleton_pullback_section f e he (K := K)
  rw [← hz', Subsingleton.elim z z']

include he in

theorem connectedSpace_pullback [Algebra.IsAlgebraic k K] [ConnectedSpace A] :
    ConnectedSpace ↥(pullback f (bc k K)) := by

  haveI : UniversallyOpen (bc k K) := inferInstance
  have hopen : IsOpenMap (pullback.fst f (bc k K)) := (pullback.fst f (bc k K)).isOpenMap

  haveI : IsIntegralHom (bc k K) := by
    rw [IsIntegralHom.SpecMap_iff, CommRingCat.hom_ofHom, algebraMap_isIntegral_iff]
    exact Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  haveI : UniversallyClosed (pullback.fst f (bc k K)) :=
    MorphismProperty.pullback_fst (P := @UniversallyClosed) _ _ inferInstance
  have hclosed : IsClosedMap (pullback.fst f (bc k K)) := (pullback.fst f (bc k K)).isClosedMap

  obtain ⟨x₁, hx₁def⟩ : ∃ x : ↥(pullback f (bc k K)), x = pt' f e he (IsLocalRing.closedPoint K) :=
    ⟨_, rfl⟩

  have key : ∀ s : Set ↥(pullback f (bc k K)), IsClopen s → x₁ ∈ s → s = Set.univ := by
    intro s hs hxs
    have himg : IsClopen (pullback.fst f (bc k K) '' sᶜ) :=
      ⟨hclosed _ hs.compl.isClosed, hopen _ hs.compl.isOpen⟩
    rcases isClopen_iff.mp himg with h0 | h1
    · exact Set.compl_empty_iff.mp (Set.image_eq_empty.mp h0)
    · exfalso
      have hmem : e (IsLocalRing.closedPoint k) ∈ pullback.fst f (bc k K) '' sᶜ :=
        h1 ▸ Set.mem_univ _
      obtain ⟨v, hvs, hv⟩ := hmem
      have hv' : v = x₁ := hx₁def ▸ eq_pt'_of_fst_eq f e he v hv
      rw [hv'] at hvs
      exact hvs hxs
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨x₁⟩, fun s hs => ?_⟩
  by_cases hxs : x₁ ∈ s
  · exact Or.inr (key s hs hxs)
  · exact Or.inl (Set.compl_univ_iff.mp (key sᶜ hs.compl hxs))

end Stacks04KV

end S17A0
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0"

open S17A0 in
theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f) : GeometricallyIntegral f := by
  haveI : Smooth f := hA.smooth
  obtain ⟨L⟩ := hA.hasGroupLaw

  let e : Spec (CommRingCat.of k) ⟶ A := (L.one (𝟙 _)).1
  have he : e ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

  haveI : ConnectedSpace ↥A := by
    rw [connectedSpace_iff_univ]
    convert hA.connectedFibres (IsLocalRing.closedPoint k) using 1
    exact (Set.eq_univ_of_forall fun a =>
      Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))).symm

  let K := AlgebraicClosure k
  haveI : ConnectedSpace ↥(pullback f (bc k K)) := connectedSpace_pullback f e he
  haveI : Smooth (pullback.snd f (bc k K)) := MorphismProperty.pullback_snd (P := @Smooth) _ _ hA.smooth
  haveI : IsIntegral (pullback f (bc k K)) :=
    isIntegral_of_smooth_of_connectedSpace (pullback.snd f (bc k K))
  haveI : LocallyOfFiniteType (pullback.snd f (bc k K)) := inferInstance
  haveI : GeometricallyIntegral (pullback.snd f (bc k K)) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI : GeometricallyConnected (pullback.snd f (bc k K)) :=
    AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected _
  haveI : MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u})
      @Surjective :=
    AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
  have hsurj : Surjective (bc k K) := ⟨Function.surjective_to_subsingleton _⟩
  haveI : GeometricallyConnected f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @GeometricallyConnected)
      (Q := @Surjective) hsurj ‹_›

  refine ⟨fun K' _ y Z fst snd h => ?_⟩
  haveI : Smooth (pullback.snd f y) := MorphismProperty.pullback_snd (P := @Smooth) _ _ hA.smooth
  haveI : ConnectedSpace ↥(pullback f y) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)
  haveI : IsIntegral (pullback f y) := isIntegral_of_smooth_of_connectedSpace (pullback.snd f y)
  exact IsIntegral.of_isIso h.isoPullback.inv

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral (solution)
