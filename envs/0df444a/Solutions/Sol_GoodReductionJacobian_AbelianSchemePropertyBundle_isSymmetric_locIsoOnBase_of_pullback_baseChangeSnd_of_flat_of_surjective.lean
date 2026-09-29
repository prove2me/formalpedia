-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.isSymmetric_locIsoOnBase_of_pullback_baseChangeSnd_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/43a3f60a-cc23-5cd2-9f28-92d552698178

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_of_pullback_of_faithfullyFlat_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isSymmetric_locIsoOnBase_of_pullback_baseChangeSnd_of_flat_of_surjective
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

noncomputable section

namespace SymRootFF

theorem mul_coe_congr {S : Type} [CommRing S] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

def pbComp {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅ (Scheme.Modules.pullback (a ≫ b)).obj M :=
  (Scheme.Modules.pullbackComp a b).app M

theorem locIsoOnBase_congr {S : Type} [CommRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S))
    {M₁ N₁ M₂ N₂ : X.Modules} (e₁ : M₁ ≅ N₁) (e₂ : M₂ ≅ N₂) (h : LocIsoOnBase g M₁ M₂) :
    LocIsoOnBase g N₁ N₂ := by
  intro s
  obtain ⟨U, hs, ⟨i⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e₁.symm ≪≫ i ≪≫ (Scheme.Modules.pullback _).mapIso e₂⟩⟩

theorem over_comp {B Y X : Scheme.{0}} {t : Y ⟶ B} {f : X ⟶ B} (x : SchemeHomOver t f) : x.1 ≫ f = t := x.2

theorem over_comp_assoc {B Y X Z : Scheme.{0}} {t : Y ⟶ B} {f : X ⟶ B} (x : SchemeHomOver t f) (h : B ⟶ Z) :
    x.1 ≫ f ≫ h = t ≫ h := by
  rw [← Category.assoc, x.2]

section

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
  (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
  (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')

def ψ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B))) :=
  ⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩

include hφ in
theorem spec_φ_comp : Spec.map (CommRingCat.ofHom φ) ≫ (Spec.map (CommRingCat.ofHom (algebraMap S B))) = (Spec.map (CommRingCat.ofHom (algebraMap S B'))) := (ψ B B' φ hφ).2

theorem g_fst : RelPicard.baseChangeSnd f (ψ B B' φ hφ) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem g_snd : RelPicard.baseChangeSnd f (ψ B B' φ hφ) ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))) =
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))) ≫ Spec.map (CommRingCat.ofHom φ) :=
  pullback.lift_snd _ _ _

theorem compat (B : Type) [CommRing B] [Algebra S B] (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of B))
    (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))) :
    ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))).mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))) =
      (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1 :=
  congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul (Spec.map (CommRingCat.ofHom (algebraMap S B))) L t' P Q)

theorem g_negMor : RelPicard.baseChangeSnd f (ψ B B' φ hφ) ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) =
    negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ≫ RelPicard.baseChangeSnd f (ψ B B' φ hφ) :=
  RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible L B B' φ hφ _ _ (compat f L B) (compat f L B') _
    (g_fst f B B' φ hφ) (g_snd f B B' φ hφ)

theorem main (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (hflat : φ.Flat) (hsurj : Function.Surjective (PrimeSpectrum.comap φ))
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj M) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))).obj 𝓛)
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj M) ⊗
          (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ))).obj M))) :
    IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) := by
  letI : Algebra B B' := φ.toAlgebra
  haveI : Module.FaithfullyFlat B B' :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp ((RingHom.FaithfullyFlat.iff_flat_and_comap_surjective).mpr ⟨hflat, hsurj⟩)
  have hgB : IsPullback (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (Spec.map (CommRingCat.ofHom (algebraMap B B'))) :=
    RelPicard.isPullback_baseChangeSnd f (ψ B B' φ hφ)

  have hAB : AbelianSchemePropertyBundle B (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) := hA.of_isPullback (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
  haveI : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) := hAB.proper
  obtain ⟨hS, hR⟩ := h
  refine ⟨?_, ?_⟩
  ·
    refine LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated B' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) hgB
      (fun T _ _ => hAB.bijective_algebraMap_sections_pullback T) _ _ (hM.pullback _) hM ?_
    refine locIsoOnBase_congr _ ?_ (Iso.refl _) hS
    exact pbComp _ _ M ≪≫ (Scheme.Modules.pullbackCongr (g_negMor f L B B' φ hφ).symm).app M ≪≫ (pbComp _ _ M).symm
  ·
    obtain ⟨e₂⟩ := nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq f L (algebraMap S B) (algebraMap S B') φ hφ (RelPicard.baseChangeSnd f (ψ B B' φ hφ))
      (g_fst f B B' φ hφ) (g_snd f B B' φ hφ) M
    refine LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated B' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B')))) (RelPicard.baseChangeSnd f (ψ B B' φ hφ)) hgB
      (fun T _ _ => hAB.bijective_algebraMap_sections_pullback T) _ _ (h𝓛.pullback _)
      (hM.tensor_monoidalV2 (hM.pullback _)) ?_
    refine locIsoOnBase_congr _ ?_ e₂.symm hR
    exact (Scheme.Modules.pullbackCongr (g_fst f B B' φ hφ).symm).app 𝓛 ≪≫ (pbComp _ _ 𝓛).symm

end

end SymRootFF

end

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra S B] [Algebra S B']
    (φ : B →+* B') (hφ : φ.comp (algebraMap S B) = algebraMap S B')
    (hflat : φ.Flat) (hsurj : Function.Surjective (PrimeSpectrum.comap φ))
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))) ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))).obj 𝓛)
        (((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B'))))
            (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B')))))).obj ((Scheme.Modules.pullback (RelPicard.baseChangeSnd f
          (⟨Spec.map (CommRingCat.ofHom φ), by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S B'))) (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M))) :
    IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
        (M ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
            (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) :=
  SymRootFF.main f L B B' φ hφ hA 𝓛 h𝓛 hflat hsurj M hM h

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_isSymmetric_locIsoOnBase_of_pullback_baseChangeSnd_of_flat_of_surjective
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isSymmetric_locIsoOnBase_of_pullback_baseChangeSnd_of_flat_of_surjective (solution)
