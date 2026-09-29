-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8add2d58-1dd2-5539-9c9a-348fe796e993

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

open CategoryTheory.Limits

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hA : AbelianSchemePropertyBundle B f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (u v : A ⟶ A) (hu : u ≫ f = f) (hv : v ≫ f = f)
    (hue : (L.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ u = (L.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (hve : (L.one (𝟙 (Spec (CommRingCat.of B)))).1 ≫ v = (L.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (w : pullback f f ⟶ pullback f f)
    (hw₁ : w ≫ pullback.fst f f = pullback.fst f f ≫ u) (hw₂ : w ≫ pullback.snd f f = pullback.snd f f ≫ v) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))))).obj
        ((Scheme.Modules.pullback w).obj (mumfordBundle f L 𝓛)) ≅ 𝟙_ _) ∧
    Nonempty ((Scheme.Modules.pullback (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj
          ((Scheme.Modules.pullback w).obj (mumfordBundle f L 𝓛))) ≅ 𝟙_ _) := by
  classical

  have he : Nonempty ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of B)))).1).obj 𝓛 ≅ 𝟙_ _) := by
    have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of B)))).1).obj 𝓛) :=
      h𝓛.pullback _
    obtain ⟨U, hU, ⟨t⟩⟩ := hN.1 (IsLocalRing.closedPoint B)
    have hUtop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hU
    subst hUtop
    exact ⟨(Scheme.Modules.pullbackId _).symm.app _ ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.toIso_inv_ι _).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso t ≪≫ Scheme.Modules.pullbackUnitIso _⟩
  obtain ⟨⟨a₀⟩, ⟨b₀⟩⟩ :=
    nonempty_sliceAt_one_mumfordBundle_iso_unit_and_swap_of_pullback_one_iso_unit f L 𝓛 h𝓛 he

  let uS : pullback f (𝟙 (Spec (CommRingCat.of B))) ⟶ pullback f (𝟙 (Spec (CommRingCat.of B))) :=
    pullback.lift (pullback.fst f _ ≫ u) (pullback.snd f _) (by rw [Category.assoc, hu]; exact pullback.condition)
  let vS : pullback f (𝟙 (Spec (CommRingCat.of B))) ⟶ pullback f (𝟙 (Spec (CommRingCat.of B))) :=
    pullback.lift (pullback.fst f _ ≫ v) (pullback.snd f _) (by rw [Category.assoc, hv]; exact pullback.condition)
  have hA : sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))) ≫ w =
      uS ≫ sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hw₁, Category.assoc]
      simp only [sliceAt, uS, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, hw₂, Category.assoc]
      simp only [sliceAt, uS, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, hve]
  have hB : sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))) ≫ (pullbackSymmetry f f).hom ≫ w =
      vS ≫ sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))) ≫ (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hw₁, ← Category.assoc ((pullbackSymmetry f f).hom), pullbackSymmetry_hom_comp_fst,
        Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst]
      simp only [sliceAt, vS, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, hue]
    · rw [Category.assoc, Category.assoc, hw₂, ← Category.assoc ((pullbackSymmetry f f).hom), pullbackSymmetry_hom_comp_snd,
        Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
      simp only [sliceAt, vS, pullback.lift_fst, pullback.lift_fst_assoc]
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hA).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ (Scheme.Modules.pullback uS).mapIso a₀ ≪≫
      Scheme.Modules.pullbackUnitIso uS
  · exact (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp _ _).app _) ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hB).app _ ≪≫
      ((Scheme.Modules.pullbackComp vS (sliceAt f (L.one (𝟙 (Spec (CommRingCat.of B)))) ≫ (pullbackSymmetry f f).hom)).app _).symm ≪≫
      (Scheme.Modules.pullback vS).mapIso (((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ b₀) ≪≫
      Scheme.Modules.pullbackUnitIso vS

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_pullback_sliceAt_one_pullback_mumfordBundle_iso_unit_of_comp_one_eq (solution)
