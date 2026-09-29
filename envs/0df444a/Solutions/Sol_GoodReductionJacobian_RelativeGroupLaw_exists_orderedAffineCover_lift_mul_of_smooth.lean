-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_orderedAffineCover_lift_mul_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c5ce7be3-c151-5694-a7ac-3eec357bde6c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_lift_mul_of_smooth

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

namespace E163K2L

@[reassoc]
theorem isoSpec_hom_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.isoSpec.hom ≫ hU.fromSpec = U.ι := by
  rw [IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]

section Chart

variable {T' T : Type u} [CommRing T'] [CommRing T]

theorem algebraMap_basicOpen {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) {Q : P.Opens}
    (a : Γ(P, Q)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p Q
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p (P.basicOpen a)
    algebraMap T' Γ(P, P.basicOpen a) =
      (algebraMap Γ(P, Q) Γ(P, P.basicOpen a)).comp (algebraMap T' Γ(P, Q)) := by
  change ((Scheme.ΓSpecIso (.of T')).inv ≫ p.appLE ⊤ (P.basicOpen a) le_top).hom =
    (P.presheaf.map (homOfLE (P.basicOpen_le a)).op).hom.comp
      ((Scheme.ΓSpecIso (.of T')).inv ≫ p.appLE ⊤ Q le_top).hom
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

theorem lift_basicOpen (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) (μ : P₀ ⟶ A)
    (Q : P.Opens) (hQ : IsAffineOpen Q)
    (εQ : letI := Scheme.TwoAffineOpenCover.algebraOfHom p Q
      Spec (CommRingCat.of (Γ(P, Q) ⧸ (RingHom.ker π).map (algebraMap T' Γ(P, Q)))) ≅ ↑(G ⁻¹ᵁ Q))
    (hεQ : letI := Scheme.TwoAffineOpenCover.algebraOfHom p Q
      εQ.hom ≫ G ∣_ Q ≫ hQ.isoSpec.hom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, Q))))))
    (a : Γ(P, Q)) (x : Spec (CommRingCat.of (Localization.Away a)) ⟶ A)
    (hx1 : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(P, Q) (Localization.Away a))) ≫
      hQ.isoSpec.inv ≫ Q.ι ≫ p)
    (hx2 : letI := Scheme.TwoAffineOpenCover.algebraOfHom p Q
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (((RingHom.ker π).map (algebraMap T' Γ(P, Q))).map (algebraMap Γ(P, Q) (Localization.Away a))))) ≫ x =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        (((RingHom.ker π).map (algebraMap T' Γ(P, Q))).map (algebraMap Γ(P, Q) (Localization.Away a)))
        (algebraMap Γ(P, Q) (Localization.Away a)) Ideal.le_comap_map)) ≫ εQ.hom ≫ (G ⁻¹ᵁ Q).ι ≫ μ) :
    ∃ m : (↑(P.basicOpen a) : Scheme.{u}) ⟶ A,
      m ≫ f = (P.basicOpen a).ι ≫ p ∧ G ∣_ (P.basicOpen a) ≫ m = (G ⁻¹ᵁ (P.basicOpen a)).ι ≫ μ := by
  letI iQ := Scheme.TwoAffineOpenCover.algebraOfHom p Q
  letI iD := Scheme.TwoAffineOpenCover.algebraOfHom p (P.basicOpen a)
  have hD : IsAffineOpen (P.basicOpen a) := hQ.basicOpen a
  haveI := hQ.isLocalization_basicOpen a
  haveI : IsClosedImmersion G :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) hG.flip
      (IsClosedImmersion.spec_of_surjective _ hπ)

  obtain ⟨-, εD, hεD⟩ :=
    AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker p p₀ G hG
      (P.basicOpen a) hD

  let locφ : Localization.Away a →+* Γ(P, P.basicOpen a) :=
    (Localization.algEquiv (Submonoid.powers a) Γ(P, P.basicOpen a)).toRingHom
  have hres : locφ.comp (algebraMap Γ(P, Q) (Localization.Away a)) = algebraMap Γ(P, Q) Γ(P, P.basicOpen a) :=
    RingHom.ext fun r => (Localization.algEquiv (Submonoid.powers a) Γ(P, P.basicOpen a)).commutes r
  have hres' : (algebraMap Γ(P, Q) Γ(P, P.basicOpen a)) = (P.presheaf.map (homOfLE (P.basicOpen_le a)).op).hom :=
    rfl
  have hφD := algebraMap_basicOpen p a

  have hJ : (((RingHom.ker π).map (algebraMap T' Γ(P, Q))).map (algebraMap Γ(P, Q) (Localization.Away a))).map
      locφ = (RingHom.ker π).map (algebraMap T' Γ(P, P.basicOpen a)) := by
    rw [Ideal.map_map, Ideal.map_map, hres, ← hφD]
  let qbar : Localization.Away a ⧸ ((RingHom.ker π).map (algebraMap T' Γ(P, Q))).map
      (algebraMap Γ(P, Q) (Localization.Away a)) →+* Γ(P, P.basicOpen a) ⧸
        (RingHom.ker π).map (algebraMap T' Γ(P, P.basicOpen a)) :=
    Ideal.quotientMap _ locφ (hJ ▸ Ideal.le_comap_map)

  refine ⟨hD.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom locφ) ≫ x, ?_, ?_⟩
  ·
    rw [Category.assoc, Category.assoc, hx1, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hres, hres',
      CommRingCat.ofHom_hom, ← Category.assoc hQ.isoSpec.inv Q.ι p, IsAffineOpen.isoSpec_inv_ι,
      hQ.map_fromSpec_assoc hD, isoSpec_hom_fromSpec_assoc]
  ·
    have hring : CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, Q)))) ≫
        CommRingCat.ofHom (Ideal.quotientMap
          (((RingHom.ker π).map (algebraMap T' Γ(P, Q))).map (algebraMap Γ(P, Q) (Localization.Away a)))
          (algebraMap Γ(P, Q) (Localization.Away a)) Ideal.le_comap_map) ≫ CommRingCat.ofHom qbar =
        P.presheaf.map (homOfLE (P.basicOpen_le a)).op ≫
          CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, P.basicOpen a)))) := by
      ext r
      change qbar (Ideal.quotientMap _ (algebraMap Γ(P, Q) (Localization.Away a)) Ideal.le_comap_map
        (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ ((P.presheaf.map (homOfLE (P.basicOpen_le a)).op).hom r)
      rw [Ideal.quotientMap_mk]
      change Ideal.quotientMap _ locφ (hJ ▸ Ideal.le_comap_map) (Ideal.Quotient.mk _ _) = _
      rw [Ideal.quotientMap_mk, ← hres', ← hres]
      rfl
    have hsq : CommRingCat.ofHom locφ ≫
        CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, P.basicOpen a)))) =
        CommRingCat.ofHom (Ideal.Quotient.mk (((RingHom.ker π).map (algebraMap T' Γ(P, Q))).map
          (algebraMap Γ(P, Q) (Localization.Away a)))) ≫ CommRingCat.ofHom qbar := by
      rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom (Ideal.quotientMap_comp_mk (hJ ▸ Ideal.le_comap_map)).symm
    have key : Spec.map (CommRingCat.ofHom qbar) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        (((RingHom.ker π).map (algebraMap T' Γ(P, Q))).map (algebraMap Γ(P, Q) (Localization.Away a)))
        (algebraMap Γ(P, Q) (Localization.Away a)) Ideal.le_comap_map)) ≫ εQ.hom ≫ (G ⁻¹ᵁ Q).ι =
        εD.hom ≫ (G ⁻¹ᵁ (P.basicOpen a)).ι := by
      rw [← cancel_mono G]
      simp only [Category.assoc]
      rw [← morphismRestrict_ι, ← morphismRestrict_ι, ← isoSpec_hom_fromSpec hQ,
        ← isoSpec_hom_fromSpec hD, reassoc_of% hεQ, reassoc_of% hεD, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, hring, Spec.map_comp_assoc, hQ.map_fromSpec hD]
    rw [← cancel_epi εD.hom, reassoc_of% hεD, ← Spec.map_comp_assoc, hsq,
      Spec.map_comp_assoc, hx2, reassoc_of% key]

end Chart

end E163K2L

namespace E163K2L

section Assemble

variable {T' T : Type u} [CommRing T'] [CommRing T]

theorem isPullback_prodMap {S S' A A₀ : Scheme.{u}} (s : S ⟶ S') (f : A ⟶ S') (f₀ : A₀ ⟶ S) (g : A₀ ⟶ A)
    (hg : IsPullback g f₀ f s)
    (w : (pullback.fst f₀ f₀ ≫ g) ≫ f = (pullback.snd f₀ f₀ ≫ g) ≫ f) :
    IsPullback (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g) w)
      (pullback.fst f₀ f₀ ≫ f₀) (pullback.fst f f ≫ f) s := by
  refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_) (fun c => ?_)
    (fun c m h₁ h₂ => ?_))
  · rw [← Category.assoc, pullback.lift_fst, Category.assoc, hg.w, Category.assoc]
  · exact pullback.lift
      (hg.lift (c.fst ≫ pullback.fst f f) c.snd (by rw [Category.assoc]; exact c.condition))
      (hg.lift (c.fst ≫ pullback.snd f f) c.snd
        (by rw [Category.assoc, ← pullback.condition]; exact c.condition))
      (by rw [hg.lift_snd, hg.lift_snd])
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hg.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hg.lift_fst]
  · change _ ≫ pullback.fst f₀ f₀ ≫ f₀ = c.snd
    rw [← Category.assoc, pullback.lift_fst, hg.lift_snd]
  · apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply hg.hom_ext
      · rw [hg.lift_fst, Category.assoc, ← pullback.lift_fst (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g) w,
          ← Category.assoc, h₁]
      · rw [hg.lift_snd, Category.assoc]
        exact h₂
    · rw [pullback.lift_snd]
      apply hg.hom_ext
      · rw [hg.lift_fst, Category.assoc, ← pullback.lift_snd (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g) w,
          ← Category.assoc, h₁]
      · rw [hg.lift_snd, Category.assoc, ← pullback.condition]
        exact h₂

theorem chart_lifts (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) [Smooth f] (μ : P₀ ⟶ A)
    (hμ : μ ≫ f = p₀ ≫ Spec.map (CommRingCat.ofHom π))
    (Q : P.Opens) (hQ : IsAffineOpen Q) :
    ∃ (ι : Type u) (a : ι → Γ(P, Q)) (c : ι →₀ Γ(P, Q)), (c.sum fun i r => r • a i) = 1 ∧
      ∀ i, ∃ m : (↑(P.basicOpen (a i)) : Scheme.{u}) ⟶ A,
        m ≫ f = (P.basicOpen (a i)).ι ≫ p ∧ G ∣_ (P.basicOpen (a i)) ≫ m = (G ⁻¹ᵁ (P.basicOpen (a i))).ι ≫ μ := by
  letI iQ := Scheme.TwoAffineOpenCover.algebraOfHom p Q
  obtain ⟨hJ, εQ, hεQ⟩ :=
    AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker p p₀ G hG Q hQ
  have hx₀ : (εQ.hom ≫ (G ⁻¹ᵁ Q).ι ≫ μ) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, Q))))) ≫
        hQ.isoSpec.inv ≫ Q.ι ≫ p := by
    rw [← hεQ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hμ, morphismRestrict_ι_assoc, hG.w]
  obtain ⟨ι, a, hspan, hx⟩ :=
    AlgebraicGeometry.Smooth.exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent f
      ((RingHom.ker π).map (algebraMap T' Γ(P, Q))) hJ (hQ.isoSpec.inv ≫ Q.ι ≫ p)
      (εQ.hom ≫ (G ⁻¹ᵁ Q).ι ≫ μ) hx₀
  have h1 : (1 : Γ(P, Q)) ∈ Ideal.span (Set.range a) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  refine ⟨ι, a, c, hc, fun i => ?_⟩
  obtain ⟨x, hx1, hx2⟩ := hx i
  exact lift_basicOpen π hπ hker p p₀ G hG f μ Q hQ εQ hεQ (a i) x hx1 hx2

theorem cover_lifts (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {P P₀ A : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (f : A ⟶ Spec (CommRingCat.of T')) [Smooth f] (μ : P₀ ⟶ A)
    (hμ : μ ≫ f = p₀ ≫ Spec.map (CommRingCat.ofHom π)) [CompactSpace ↥P] :
    ∃ (𝒲 : P.OrderedAffineCover) (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A),
      (∀ i, m i ≫ f = (𝒲.U i).ι ≫ p) ∧ (∀ i, G ∣_ (𝒲.U i) ≫ m i = (G ⁻¹ᵁ (𝒲.U i)).ι ≫ μ) := by
  classical

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : P.affineOpens => ((U : P.Opens) : Set P))
    (fun U => (U : P.Opens).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : P.affineOpens, (U : P.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)

  have chart := fun j : ↥t =>
    chart_lifts π hπ hker p p₀ G hG f μ hμ (j.1 : P.Opens) j.1.2
  choose ιj a c hc mdata using chart
  choose m hm1 hm2 using mdata

  let I : Type u := Σ j : ↥t, ↥(c j).support
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hcov : ⨆ i : I, P.basicOpen (a i.1 i.2.1) = ⊤ := by
    rw [← top_le_iff]
    intro x _
    obtain ⟨j₀, hj₀, hxj⟩ : ∃ j ∈ t, x ∈ ((j : P.Opens) : Set P) := by
      simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
    let j : ↥t := ⟨j₀, hj₀⟩
    have hS : Ideal.span ((fun k => a j k) '' (↑(c j).support : Set (ιj j))) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← hc j, Finsupp.sum]
      exact Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    have hQeq := (j₀.2.iSup_basicOpen_eq_self_iff).mpr hS
    have hxQ : x ∈ ⨆ s : ↥((fun k => a j k) '' (↑(c j).support : Set (ιj j))), P.basicOpen (s : Γ(P, j₀)) := by
      rw [hQeq]; exact hxj
    obtain ⟨⟨_, k, hk, rfl⟩, hxk⟩ := TopologicalSpace.Opens.mem_iSup.mp hxQ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j, ⟨k, hk⟩⟩, hxk⟩
  exact ⟨Scheme.OrderedAffineCover.mk I (fun i => P.basicOpen (a i.1 i.2.1)) (fun i => i.1.1.2.basicOpen _) hcov,
    fun i => m i.1 i.2.1, fun i => hm1 i.1 i.2.1, fun i => hm2 i.1 i.2.1⟩

end Assemble

end E163K2L

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π))) :
    ∃ (𝒲 : (pullback f f).OrderedAffineCover) (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A),
      (∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f) ∧
      (∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g) := by
  haveI := hs
  haveI := hp
  haveI : CompactSpace ↥A := QuasiCompact.compactSpace_of_compactSpace f
  have hG := E163K2L.isPullback_prodMap (Spec.map (CommRingCat.ofHom π)) f f₀ g hg
    (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hμ : ((L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩
      ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g) ≫ f =
      (pullback.fst f₀ f₀ ≫ f₀) ≫ Spec.map (CommRingCat.ofHom π) := by
    rw [Category.assoc, hg.w, ← Category.assoc,
      (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).2]
  obtain ⟨𝒲, m, h1, h2⟩ := E163K2L.cover_lifts π hπ hker (pullback.fst f f ≫ f) (pullback.fst f₀ f₀ ≫ f₀) _ hG f _ hμ
  exact ⟨𝒲, m, h1, h2⟩

#print axioms solution

end S_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_lift_mul_of_smooth
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_lift_mul_of_smooth (solution)
