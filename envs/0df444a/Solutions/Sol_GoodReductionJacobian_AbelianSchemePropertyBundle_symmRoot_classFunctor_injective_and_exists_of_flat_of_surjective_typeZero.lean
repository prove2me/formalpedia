-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4e666407-938b-5697-b0d5-31b45be10fc7

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor

import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_of_isAffineHom_of_flat_of_surjective_of_bijective_sections
import Theorems.Thm_AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isSymmetric_locIsoOnBase_of_pullback_baseChangeSnd_of_flat_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SymmRoot"

noncomputable section

namespace RootSheaf

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem locIsoOnBase_congr {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    {M₁ N₁ M₂ N₂ : X.Modules} (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (h : LocIsoOnBase g M₁ M₂) :
    LocIsoOnBase g N₁ N₂ := by
  intro s
  obtain ⟨U, hs, ⟨i⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e₁.symm ≪≫ i ≪≫ (Scheme.Modules.pullback _).mapIso e₂⟩⟩

theorem symmRootPred_congr (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (R₀ : Type) [CommRing R₀] [Algebra S R₀]
    (B : Under (CommRingCat.of R₀)) {M M' : (pullback f (ι S R₀ B)).Modules} (e : M ≅ M')
    (h : symmRootPred L 𝓛 R₀ B M) : symmRootPred L 𝓛 R₀ B M' :=
  ⟨locIsoOnBase_congr _ ((Scheme.Modules.pullback _).mapIso e) e h.1,
    locIsoOnBase_congr _ (Iso.refl _) (e ⊗ᵢ (Scheme.Modules.pullback _).mapIso e) h.2⟩

theorem pullbackAlong_iso_of_pushout (R₀ : Type) [CommRing R₀] [Algebra S R₀]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (M' : RigidifiedLineBundle f ε (ι S R₀ B'))
    (hyp : Nonempty ((M'.pullbackAlong (ψ S R₀ (pushout.inl φ φ))).L ≅ (M'.pullbackAlong (ψ S R₀ (pushout.inr φ φ))).L))
    (Z : Scheme.{0}) (z : Z ⟶ Spec (CommRingCat.of S)) (p₁ p₂ : SchemeHomOver z (ι S R₀ B'))
    (hp : p₁.1 ≫ (ψ S R₀ φ).1 = p₂.1 ≫ (ψ S R₀ φ).1) :
    Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L) := by
  obtain ⟨e⟩ := hyp
  have hP := AlgebraicGeometry.isPullback_Spec_map_pushout_inl_right_inr_right φ φ
  let r : Z ⟶ Spec (CommRingCat.of (pushout φ φ).right) := hP.lift p₁.1 p₂.1 hp
  have hr₁ : r ≫ (ψ S R₀ (pushout.inl φ φ)).1 = p₁.1 := hP.lift_fst _ _ _
  have hr₂ : r ≫ (ψ S R₀ (pushout.inr φ φ)).1 = p₂.1 := hP.lift_snd _ _ _
  let ρ : SchemeHomOver z (ι S R₀ (pushout φ φ)) :=
    ⟨r, by rw [← (ψ S R₀ (pushout.inl φ φ)).2, ← Category.assoc, hr₁]; exact p₁.2⟩
  have hb₁ : baseChangeSnd f p₁ = baseChangeSnd f ρ ≫ baseChangeSnd f (ψ S R₀ (pushout.inl φ φ)) := by
    rw [baseChangeSnd_comp]; congr 1; exact Subtype.ext hr₁.symm
  have hb₂ : baseChangeSnd f p₂ = baseChangeSnd f ρ ≫ baseChangeSnd f (ψ S R₀ (pushout.inr φ φ)) := by
    rw [baseChangeSnd_comp]; congr 1; exact Subtype.ext hr₂.symm
  exact ⟨(Scheme.Modules.pullbackCongr hb₁).app M'.L ≪≫ ((Scheme.Modules.pullbackComp _ _).app M'.L).symm ≪≫
    (Scheme.Modules.pullback (baseChangeSnd f ρ)).mapIso e ≪≫
    (Scheme.Modules.pullbackComp _ _).app M'.L ≪≫ (Scheme.Modules.pullbackCongr hb₂.symm).app M'.L⟩

theorem main (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R₀ : Type) [CommRing R₀] [Algebra S R₀]
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι S R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ S R₀ φ)).L)
    (B B' : Under (CommRingCat.of R₀)) (φ : B ⟶ B')
    (hflat : φ.right.hom.Flat) (hsurj : Function.Surjective (PrimeSpectrum.comap φ.right.hom)) :
    Function.Injective ((classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map φ) ∧
      ∀ y : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B',
        (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map (pushout.inl φ φ) y =
          (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map (pushout.inr φ φ) y →
        ∃ x : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B,
          (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map φ x = y := by

  have hff : φ.right.hom.FaithfullyFlat := RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hflat, hsurj⟩
  obtain ⟨hfl, hsu⟩ := (flat_and_surjective_SpecMap_iff φ.right).mpr hff
  haveI : Flat (ψ S R₀ φ).1 := hfl
  haveI : Surjective (ψ S R₀ φ).1 := hsu
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨x, rfl⟩ := mk_surjective _ _ _ _ _ a
    obtain ⟨y, rfl⟩ := mk_surjective _ _ _ _ _ b
    rw [map_mk, map_mk, mk_eq_mk_iff] at hab
    rw [mk_eq_mk_iff]
    exact RigidifiedLineBundle.nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections S f
      (L.one (𝟙 _)) (fun T _ _ => hA.bijective_algebraMap_sections_pullback T) (ι S R₀ B) (ι S R₀ B') (ψ S R₀ φ)
      x.M y.M hab
  · intro yq hy
    obtain ⟨y, rfl⟩ := mk_surjective _ _ _ _ _ yq
    rw [map_mk, map_mk, mk_eq_mk_iff] at hy
    obtain ⟨M, ⟨eM⟩⟩ :=
      RigidifiedLineBundle.exists_descent_of_isAffineHom_of_flat_of_surjective_of_bijective_sections S f (L.one (𝟙 _))
        (fun T _ _ => hA.bijective_algebraMap_sections_pullback T) (ι S R₀ B) (ι S R₀ B') (ψ S R₀ φ) y.M
        (pullbackAlong_iso_of_pushout R₀ (L.one (𝟙 _)) φ y.M hy)
    have hprop' : symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (ψ S R₀ φ)).L := symmRootPred_congr L 𝓛 R₀ B' eM.symm y.prop
    have hprop : symmRootPred L 𝓛 R₀ B M.L := by
      letI := algS S R₀ B
      letI := algS S R₀ B'
      exact GoodReductionJacobian.AbelianSchemePropertyBundle.isSymmetric_locIsoOnBase_of_pullback_baseChangeSnd_of_flat_of_surjective
        L hA 𝓛 h𝓛 B.right B'.right φ.right.hom (comp_algebraMap S R₀ φ) hflat hsurj M.L M.isInvertible hprop'
    refine ⟨mk f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h) ⟨M, hprop⟩, ?_⟩
    rw [map_mk, mk_eq_mk_iff]
    exact ⟨eM⟩

end RootSheaf

end

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R₀ : Type) [CommRing R₀] [Algebra S R₀]
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B')
      (M : RigidifiedLineBundle f (L.one (𝟙 _)) (SymmRoot.ι S R₀ B)),
      symmRootPred L 𝓛 R₀ B M.L → symmRootPred L 𝓛 R₀ B' (M.pullbackAlong (SymmRoot.ψ S R₀ φ)).L)
    (B B' : Under (CommRingCat.of R₀)) (φ : B ⟶ B')
    (hflat : φ.right.hom.Flat) (hsurj : Function.Surjective (PrimeSpectrum.comap φ.right.hom)) :
    Function.Injective ((classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map φ) ∧
      ∀ y : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B',
        (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map (pushout.inl φ φ) y =
          (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map (pushout.inr φ φ) y →
        ∃ x : (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).obj B,
          (classFunctor f (L.one (𝟙 _)) R₀ (symmRootStablePred L 𝓛 R₀ h)).map φ x = y :=
  RootSheaf.main L hA 𝓛 h𝓛 R₀ h B B' φ hflat hsurj

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_symmRoot_classFunctor_injective_and_exists_of_flat_of_surjective_typeZero (solution)
