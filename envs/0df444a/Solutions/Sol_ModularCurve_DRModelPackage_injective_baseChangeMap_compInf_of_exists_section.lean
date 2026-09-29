-- Prove2me | solution 1 for ModularCurve.DRModelPackage.injective_baseChangeMap_compInf_of_exists_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b72e4250-310d-5202-8d13-485a8c751ddb

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
import Theorems.Thm_ModularCurve_DRModel_isIso_residueFieldMap_snd_baseChangeMap_residue_apply
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_injective_baseChangeMap_compInf_of_exists_section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsLocalRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (hrat : ∀ x : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        (DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base x) =
          (DRModel.baseChangeMap (IsLocalRing.residue O)).base
            (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)))) :
    Function.Injective fun n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)) =>
      (DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base n) := by
  haveI := 𝔛.compInf_isClosedImmersion κ
  haveI := 𝔛.compZero_isClosedImmersion κ
  intro n m hnm
  simp only at hnm

  haveI : IsClosedImmersion (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ) := inferInstance
  apply (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).isClosedEmbedding.injective

  have hspec : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (RingHom.ext_int _ _)
  let e : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ≅
      pullback (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
        (Spec.map (CommRingCat.ofHom toκ)) :=
    pullback.congrHom rfl hspec.symm ≪≫
      (pullbackLeftPullbackSndIso (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
        (Spec.map (CommRingCat.ofHom toκ))).symm
  have he : e.hom ≫ pullback.fst _ _ = DRModel.baseChangeMap (p := p) toκ := by
    apply pullback.hom_ext
    · calc (e.hom ≫ pullback.fst _ _) ≫ pullback.fst _ _
          = (pullback.congrHom rfl hspec.symm).hom ≫
              ((pullbackLeftPullbackSndIso (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
                (Spec.map (CommRingCat.ofHom toκ))).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _) := by
            simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
        _ = (pullback.congrHom rfl hspec.symm).hom ≫ pullback.fst _ _ := by
            rw [pullbackLeftPullbackSndIso_inv_fst]
        _ = pullback.fst _ _ ≫ 𝟙 _ := pullback.lift_fst _ _ _
        _ = DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    · calc (e.hom ≫ pullback.fst _ _) ≫ pullback.snd _ _
          = (pullback.congrHom rfl hspec.symm).hom ≫
              ((pullbackLeftPullbackSndIso (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
                (Spec.map (CommRingCat.ofHom toκ))).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _) := by
            simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
        _ = (pullback.congrHom rfl hspec.symm).hom ≫ (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ)) := by
            rw [pullbackLeftPullbackSndIso_inv_fst_snd]
        _ = ((pullback.congrHom rfl hspec.symm).hom ≫ pullback.snd _ _) ≫ Spec.map (CommRingCat.ofHom toκ) :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd _ _ ≫ 𝟙 _) ≫ Spec.map (CommRingCat.ofHom toκ) :=
            congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom toκ)) (pullback.lift_snd _ _ _)
        _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := by rw [Category.comp_id]
        _ = DRModel.baseChangeMap (p := p) toκ ≫ pullback.snd _ _ := (pullback.lift_snd _ _ _).symm
  have heapp : ∀ a, (pullback.fst (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
      (Spec.map (CommRingCat.ofHom toκ))).base (e.hom.base a) = (DRModel.baseChangeMap (p := p) toκ).base a :=
    fun a => by rw [← Scheme.Hom.comp_apply, he]

  apply e.hom.isOpenEmbedding.injective
  obtain ⟨s, hs, hx⟩ := hrat m
  haveI : IsIso ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).residueFieldMap
      ((pullback.fst (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
        (Spec.map (CommRingCat.ofHom toκ))).base
        (e.hom.base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base m)))) := by
    rw [heapp, hx]
    exact ModularCurve.DRModel.isIso_residueFieldMap_snd_baseChangeMap_residue_apply p O s hs
  exact Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
    (by rw [heapp, heapp]; exact hnm) (Subsingleton.elim _ _)

end S_ModularCurve_DRModelPackage_injective_baseChangeMap_compInf_of_exists_section
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_injective_baseChangeMap_compInf_of_exists_section (solution)
