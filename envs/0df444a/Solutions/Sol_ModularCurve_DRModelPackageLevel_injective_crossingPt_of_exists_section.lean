-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.injective_crossingPt_of_exists_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4f0e8632-2e7c-5c0b-98be-2f0e9ae2fdcc

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
import Theorems.Thm_ModularCurve_DRLevel_isIso_residueFieldMap_snd_bcMap_residue_apply
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_injective_crossingPt_of_exists_section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (hrat : ∀ n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ DRLevel.fibre (N₀ := N₀) ((IsLocalRing.residue O).comp ρO),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        𝔛.crossingPt ρO toκ n =
          (DRLevel.bcMap ρO (IsLocalRing.residue O)).base (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))) :
    Function.Injective fun n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)) => 𝔛.crossingPt ρO toκ n := by
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 0
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 1
  intro n m hnm
  simp only at hnm

  haveI : IsClosedImmersion (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0) :=
    inferInstance
  apply (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0).isClosedEmbedding.injective

  have hspec : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO) =
      Spec.map (CommRingCat.ofHom (toκ.comp ρO)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let e : DRLevel.fibre (N₀ := N₀) (toκ.comp ρO) ≅
      pullback (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) (Spec.map (CommRingCat.ofHom toκ)) :=
    pullback.congrHom rfl hspec.symm ≪≫
      (pullbackLeftPullbackSndIso (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))
        (Spec.map (CommRingCat.ofHom toκ))).symm
  have he : e.hom ≫ pullback.fst _ _ = DRLevel.bcMap (N₀ := N₀) ρO toκ := by
    apply pullback.hom_ext
    · calc (e.hom ≫ pullback.fst _ _) ≫ pullback.fst _ _
          = (pullback.congrHom rfl hspec.symm).hom ≫
              ((pullbackLeftPullbackSndIso (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))
                (Spec.map (CommRingCat.ofHom toκ))).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _) := by
            simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
        _ = (pullback.congrHom rfl hspec.symm).hom ≫ pullback.fst _ _ := by
            rw [pullbackLeftPullbackSndIso_inv_fst]
        _ = pullback.fst _ _ ≫ 𝟙 _ := pullback.lift_fst _ _ _
        _ = DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst _ _ := by
            rw [DRLevel.bcMap, pullback.map, pullback.lift_fst]
    · calc (e.hom ≫ pullback.fst _ _) ≫ pullback.snd _ _
          = (pullback.congrHom rfl hspec.symm).hom ≫
              ((pullbackLeftPullbackSndIso (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))
                (Spec.map (CommRingCat.ofHom toκ))).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _) := by
            simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
        _ = (pullback.congrHom rfl hspec.symm).hom ≫ (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ)) := by
            rw [pullbackLeftPullbackSndIso_inv_fst_snd]
        _ = ((pullback.congrHom rfl hspec.symm).hom ≫ pullback.snd _ _) ≫ Spec.map (CommRingCat.ofHom toκ) :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd _ _ ≫ 𝟙 _) ≫ Spec.map (CommRingCat.ofHom toκ) :=
            congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom toκ)) (pullback.lift_snd _ _ _)
        _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := by rw [Category.comp_id]
        _ = DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.snd _ _ := by
            rw [DRLevel.bcMap, pullback.map, pullback.lift_snd]
  have heapp : ∀ a, (pullback.fst (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
      (Spec.map (CommRingCat.ofHom toκ))).base (e.hom.base a) = (DRLevel.bcMap (N₀ := N₀) ρO toκ).base a :=
    fun a => by rw [← Scheme.Hom.comp_apply, he]

  have hnm' : (DRLevel.bcMap (N₀ := N₀) ρO toκ).base ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n)) =
      (DRLevel.bcMap (N₀ := N₀) ρO toκ).base ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base m)) := by
    simpa only [DRModelPackageLevel.crossingPt, Scheme.Hom.comp_apply] using hnm

  apply e.hom.isOpenEmbedding.injective
  obtain ⟨s, hs, hx⟩ := hrat m
  haveI : IsIso ((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).residueFieldMap
      ((pullback.fst (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
        (Spec.map (CommRingCat.ofHom toκ))).base
        (e.hom.base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0).base m)))) := by
    have hx' : (DRLevel.bcMap (N₀ := N₀) ρO toκ).base ((𝔛.comp κ (toκ.comp ρO) 0).base ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base m)) =
        (DRLevel.bcMap ρO (IsLocalRing.residue O)).base (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))) := by
      simpa only [DRModelPackageLevel.crossingPt, Scheme.Hom.comp_apply] using hx
    rw [heapp, Scheme.Hom.comp_apply, hx']
    exact ModularCurve.DRLevel.isIso_residueFieldMap_snd_bcMap_residue_apply N₀ q O ρO s hs
  refine Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap ?_ (Subsingleton.elim _ _)
  rw [heapp, heapp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact hnm'

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_injective_crossingPt_of_exists_section
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_injective_crossingPt_of_exists_section (solution)
