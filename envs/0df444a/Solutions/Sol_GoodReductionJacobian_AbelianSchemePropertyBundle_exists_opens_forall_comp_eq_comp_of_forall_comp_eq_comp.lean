-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/938cff2b-e132-5576-8e50-5c4a036a3ca4

import Mathlib
import Definitions.Def_JacJ1Iface
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_surjective_appTop_and_pullback_snd_away
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace P2mWs30OpenLocus

theorem mem_range_away_iff {R : Type} [CommRing R] (r : R) (q : PrimeSpectrum R) :
    q ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base ↔
      q ∈ PrimeSpectrum.basicOpen r := by
  have h := Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r) q
  exact h

theorem exists_basicOpen_fst_comp_eq
    {R : Type} [CommRing R] {A Y : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (τ : A ⟶ Y)
    (c : Spec (CommRingCat.of R) ⟶ Y) (e : Spec (CommRingCat.of R) ⟶ A) (he : e ≫ f = 𝟙 _) (heτ : e ≫ τ = c)
    (s : Spec (CommRingCat.of R)) (hs : ∀ a : A, f.base a = s → τ.base a = c.base s) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ≫ τ =
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ≫ f ≫ c := by
  classical
  haveI := hA.proper

  let 𝒲 := Y.affineCover
  let i := 𝒲.idx (c.base s)
  let w : 𝒲.X i ⟶ Y := 𝒲.f i
  have hwopen : IsOpen (Set.range w.base) := w.isOpenEmbedding.isOpen_range
  have hcs : c.base s ∈ Set.range w.base := 𝒲.covers (c.base s)

  let T : Set A := τ.base ⁻¹' Set.range w.base
  have hTopen : IsOpen T := hwopen.preimage τ.base.hom.continuous
  have hfib : ∀ a : A, f.base a = s → a ∈ T := fun a ha => by
    show τ.base a ∈ Set.range w.base
    rw [hs a ha]; exact hcs
  have hclosed : IsClosed (f.base '' Tᶜ) := f.isClosedMap _ hTopen.isClosed_compl
  let V : Set (Spec (CommRingCat.of R)) := (f.base '' Tᶜ)ᶜ ∩ c.base ⁻¹' Set.range w.base
  have hVopen : IsOpen V := hclosed.isOpen_compl.inter (hwopen.preimage c.base.hom.continuous)
  have hsV : s ∈ V := by
    refine ⟨?_, hcs⟩
    rintro ⟨a, ha, hfa⟩
    exact ha (hfib a hfa)

  obtain ⟨_, ⟨r, rfl⟩, hsr, hrV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hsV hVopen
  refine ⟨r, hsr, ?_⟩

  let lam := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let ιr := pullback.fst f lam
  let pr := pullback.snd f lam
  have hrange : ∀ a' : ↥(Limits.pullback f lam), f.base (ιr.base a') ∈ PrimeSpectrum.basicOpen r := by
    intro a'
    have : f.base (ιr.base a') = lam.base (pr.base a') := by
      change (ιr ≫ f).base a' = (pr ≫ lam).base a'
      rw [pullback.condition]
    rw [this]
    exact (mem_range_away_iff r _).mp ⟨_, rfl⟩

  have h1 : Set.range (ιr ≫ τ).base ⊆ Set.range w.base := by
    rintro _ ⟨a', rfl⟩
    have hV' : f.base (ιr.base a') ∈ V := hrV (hrange a')
    have : ιr.base a' ∈ T := by
      by_contra hT
      exact hV'.1 ⟨_, hT, rfl⟩
    exact this
  have h2 : Set.range (lam ≫ c).base ⊆ Set.range w.base := by
    rintro _ ⟨z, rfl⟩
    have hV' : lam.base z ∈ V := hrV ((mem_range_away_iff r _).mp ⟨_, rfl⟩)
    exact hV'.2
  let τr := IsOpenImmersion.lift w (ιr ≫ τ) h1
  let cr := IsOpenImmersion.lift w (lam ≫ c) h2
  have hτr : τr ≫ w = ιr ≫ τ := IsOpenImmersion.lift_fac _ _ _
  have hcr : cr ≫ w = lam ≫ c := IsOpenImmersion.lift_fac _ _ _

  let er : Spec (CommRingCat.of (Localization.Away r)) ⟶ Limits.pullback f lam :=
    pullback.lift (lam ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have her_ι : er ≫ ιr = lam ≫ e := pullback.lift_fst _ _ _
  have her_p : er ≫ pr = 𝟙 _ := pullback.lift_snd _ _ _
  have hsec : er ≫ τr = er ≫ pr ≫ cr := by
    rw [← cancel_mono w, Category.assoc, hτr, ← Category.assoc, her_ι, Category.assoc, heτ,
      ← Category.assoc, her_p, Category.id_comp, hcr]

  have hsurj := (hA.surjective_appTop_and_pullback_snd_away).2 r
  have hsec' : ∀ x, er.appTop (pr.appTop x) = x := by
    intro x
    have h := Scheme.Hom.comp_appTop er pr
    rw [her_p, Scheme.Hom.id_appTop] at h
    have := congrArg (fun φ => φ x) h
    simpa using this.symm
  have hc2 : ∀ (u : Limits.pullback f lam ⟶ 𝒲.X i) (v), er.appTop (u.appTop v) = (er ≫ u).appTop v := by
    intro u v
    rw [Scheme.Hom.comp_appTop]
    rfl
  have happ : τr.appTop = (pr ≫ cr).appTop := by
    apply CommRingCat.hom_ext
    ext v
    obtain ⟨x₁, hx₁⟩ := hsurj (τr.appTop v)
    obtain ⟨x₂, hx₂⟩ := hsurj ((pr ≫ cr).appTop v)
    have h1 : er.appTop (τr.appTop v) = er.appTop ((pr ≫ cr).appTop v) := by
      rw [hc2, hc2, hsec]
    have hw : x₁ = x₂ := by
      have e1 : er.appTop (pr.appTop x₁) = er.appTop (pr.appTop x₂) := by
        have a1 : pr.appTop x₁ = τr.appTop v := hx₁
        have a2 : pr.appTop x₂ = (pr ≫ cr).appTop v := hx₂
        rw [a1, a2]; exact h1
      rwa [hsec', hsec'] at e1
    have a1 : pr.appTop x₁ = τr.appTop v := hx₁
    have a2 : pr.appTop x₂ = (pr ≫ cr).appTop v := hx₂
    exact a1.symm.trans (hw ▸ a2)
  have hτr_eq : τr = pr ≫ cr := ext_of_isAffine happ
  have key : ιr ≫ τ = ιr ≫ f ≫ c := by
    rw [← hτr, hτr_eq, Category.assoc, hcr, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (pullback.condition).symm
  exact key

theorem exists_geometric_point {X : Scheme.{0}} (a : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (CommRingCat.of K) ⟶ X),
      x.base (IsLocalRing.closedPoint K) = a := by
  let k := X.residueField a
  let K := AlgebraicClosure k
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ X.fromSpecResidueField a, ?_⟩
  exact X.fromSpecResidueField_apply a _

end P2mWs30OpenLocus

open P2mWs30OpenLocus in
theorem solution
    {S : Type} [CommRing S] {A Y : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f)
    (g : Y ⟶ Spec (CommRingCat.of S)) (τ : A ⟶ Y) (hτ : τ ≫ g = f)
    (c : Spec (CommRingCat.of S) ⟶ Y) (hc : c ≫ g = 𝟙 _)
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _) (heτ : e ≫ τ = c)
    (s : ↥(Spec (CommRingCat.of S)))
    (hs : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
      f.base (x.base (IsLocalRing.closedPoint K)) = s → x ≫ τ = x ≫ f ≫ c) :
    ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
        f.base (x.base (IsLocalRing.closedPoint K)) ∈ U → x ≫ τ = x ≫ f ≫ c := by
  classical

  have hs' : ∀ a : A, f.base a = s → τ.base a = c.base s := by
    intro a ha
    obtain ⟨K, _, _, x, hx⟩ := exists_geometric_point a
    have h := hs K x (by rw [hx]; exact ha)
    have := congrArg (fun φ => φ.base (IsLocalRing.closedPoint K)) h
    change τ.base (x.base _) = c.base (f.base (x.base _)) at this
    rw [hx] at this
    rw [this, ha]
  obtain ⟨r, hsr, key⟩ := exists_basicOpen_fst_comp_eq hA τ c e he heτ s hs'
  refine ⟨PrimeSpectrum.basicOpen r, hsr, ?_⟩
  intro K _ _ x hx

  set φ : S →+* K := (Spec.preimage (x ≫ f)).hom with hφ
  have hxf : x ≫ f = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hunit : IsUnit (φ r) := by
    have h1 : (Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint K) ∈ PrimeSpectrum.basicOpen r := by
      rw [← hxf]; exact hx
    change PrimeSpectrum.comap φ (IsLocalRing.closedPoint K) ∈ PrimeSpectrum.basicOpen r at h1
    rw [PrimeSpectrum.mem_basicOpen] at h1
    change φ r ∉ (IsLocalRing.closedPoint K).asIdeal at h1
    by_contra hnu
    exact h1 ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  let μ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (Localization.Away r)) :=
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift r hunit))
  have hμ : μ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))) = x ≫ f := by
    rw [hxf, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact IsLocalization.Away.lift_comp r hunit
  let x' := pullback.lift x μ hμ.symm
  have hx' : x' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) = x :=
    pullback.lift_fst _ _ _
  rw [← hx', Category.assoc, key, Category.assoc]

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_opens_forall_comp_eq_comp_of_forall_comp_eq_comp (solution)
