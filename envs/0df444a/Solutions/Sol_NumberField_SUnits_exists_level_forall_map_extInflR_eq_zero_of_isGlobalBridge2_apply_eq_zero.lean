-- Prove2me | solution 1 for NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/050625d9-c5a8-5cad-aec2-9655e9497d46

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import Theorems.Thm_Rep_extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul
import Theorems.Thm_Rep_homSeqOne_shortExact
import Theorems.Thm_Rep_isZero_tateCohomology_ihom_free
import Theorems.Thm_Rep_finite_H1_ihom_relationModuleInt
import Theorems.Thm_NumberField_SUnits_moduleFinite_sUnitsRep
import Theorems.Thm_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow
import Theorems.Thm_IntermediateField_isUnramifiedOutside_normalClosure__721fcc
import Theorems.Thm_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Theorems.Thm_NumberField_exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_RelationModuleRes
import Theorems.Thm_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
import Theorems.Thm_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq
import Theorems.Thm_groupCohomology_exists_isGlobalBridge2
import Theorems.Thm_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "Rep.coe_tateδneg2_apply"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

namespace KD

open GroupCohomology

section generalK

universe u

variable {k G : Type u} [CommRing k] [Group G]

noncomputable def liftToImage {X Y Z : Rep.{u} k G} (f : X ⟶ Y) (h : Z ⟶ Y)
    (hh : ∀ z : Z, h.hom z ∈ LinearMap.range f.hom.toLinearMap) : Z ⟶ RepImage.obj f :=
  Rep.ofHom ⟨LinearMap.codRestrict _ h.hom.toLinearMap hh,
    fun g => LinearMap.ext fun z => Subtype.ext (Rep.hom_comm_apply h g z)⟩

theorem liftToImage_hom_apply_coe {X Y Z : Rep.{u} k G} (f : X ⟶ Y) (h : Z ⟶ Y)
    (hh : ∀ z : Z, h.hom z ∈ LinearMap.range f.hom.toLinearMap) (z : Z) :
    ((liftToImage f h hh).hom z : Y) = h.hom z := rfl

theorem liftToImage_ι {X Y Z : Rep.{u} k G} (f : X ⟶ Y) (h : Z ⟶ Y)
    (hh : ∀ z : Z, h.hom z ∈ LinearMap.range f.hom.toLinearMap) :
    liftToImage f h hh ≫ RepImage.ι f = h :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

theorem ihom_map_comp_preHom {A A' E₁ E₂ : Rep.{u} k G} (f : A ⟶ A') (φ : E₁ ⟶ E₂) :
    (ihom A').map φ ≫ Rep.preHom f E₂ = Rep.preHom f E₁ ≫ (ihom A).map φ :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => LinearMap.ext fun a => rfl)

theorem resFunctor_map_preHom_comp_resIhom {G' : Type u} [Group G'] (π : G' →* G) {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) :
    (Rep.resFunctor π).map (Rep.preHom f E) ≫ Rep.resIhom π A E = Rep.resIhom π A' E ≫ Rep.preHom ((Rep.resFunctor π).map f) (Rep.res π E) :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => LinearMap.ext fun a => rfl)

end generalK

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')

noncomputable abbrev homB : Rep.res π ((ihom B).obj E) ⟶ (ihom (Rep.res π B)).obj E' :=
  Rep.resIhom π B E ≫ (ihom (Rep.res π B)).map φ

theorem homB_hom_apply (f : Rep.res π ((ihom B).obj E)) (b : B) :
    LinearMap.toAddMonoidHom ((homB π B E E' φ).hom f) b = φ.hom (LinearMap.toAddMonoidHom (show (ihom B).obj E from f) b) := rfl

theorem extInflF_hom_apply (f : Rep.res π ((ihom (Rep.free ℤ G B)).obj E)) (y : Rep.free ℤ G' (Rep.res π B)) :
    LinearMap.toAddMonoidHom ((Rep.extInflF π B E E' φ).hom f) y =
      φ.hom (LinearMap.toAddMonoidHom (show (ihom (Rep.free ℤ G B)).obj E from f) ((Rep.freeResMap π B).hom y)) := rfl

theorem extInflR_hom_apply (f : Rep.res π ((ihom (Rep.relationModuleInt B)).obj E)) (y : Rep.relationModuleInt (Rep.res π B)) :
    LinearMap.toAddMonoidHom ((Rep.extInflR π B E E' φ).hom f) y =
      φ.hom (LinearMap.toAddMonoidHom (show (ihom (Rep.relationModuleInt B)).obj E from f) ((Rep.relationModuleInt.resMap π B).hom y)) := rfl

theorem ι_resMap_apply (y : Rep.relationModuleInt (Rep.res π B)) :
    (Rep.relationModuleInt.ι B).hom (show Rep.relationModuleInt B from (Rep.relationModuleInt.resMap π B).hom y) =
      (Rep.freeResMap π B).hom ((Rep.relationModuleInt.ι (Rep.res π B)).hom y) := rfl

theorem resMap_comp_ι :
    Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map (Rep.relationModuleInt.ι B) =
      Rep.relationModuleInt.ι (Rep.res π B) ≫ Rep.freeResMap π B :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

theorem extInflF_comp_preι :
    Rep.extInflF π B E E' φ ≫ Rep.preι (Rep.res π B) E' = (Rep.resFunctor π).map (Rep.preι B E) ≫ Rep.extInflR π B E E' φ := by
  have h4 : Rep.preHom ((Rep.resFunctor π).map (Rep.relationModuleInt.ι B)) (Rep.res π E) ≫
      Rep.preHom (Rep.relationModuleInt.resMap π B) (Rep.res π E) =
      Rep.preHom (Rep.freeResMap π B) (Rep.res π E) ≫ Rep.preHom (Rep.relationModuleInt.ι (Rep.res π B)) (Rep.res π E) := by
    rw [Rep.preHom_comp, Rep.preHom_comp, resMap_comp_ι]
  change (Rep.resIhom π (Rep.free ℤ G B) E ≫ Rep.preHom (Rep.freeResMap π B) (Rep.res π E) ≫
      (ihom (Rep.free ℤ G' (Rep.res π B))).map φ) ≫ Rep.preHom (Rep.relationModuleInt.ι (Rep.res π B)) E' =
    (Rep.resFunctor π).map (Rep.preHom (Rep.relationModuleInt.ι B) E) ≫
      Rep.resIhom π (Rep.relationModuleInt B) E ≫ Rep.preHom (Rep.relationModuleInt.resMap π B) (Rep.res π E) ≫
        (ihom (Rep.relationModuleInt (Rep.res π B))).map φ
  rw [Category.assoc, Category.assoc, ihom_map_comp_preHom, ← Category.assoc (Rep.preHom (Rep.freeResMap π B) (Rep.res π E)),
    ← h4, Category.assoc, ← Category.assoc (Rep.resIhom π (Rep.free ℤ G ↑B) E),
    ← resFunctor_map_preHom_comp_resIhom, Category.assoc]

noncomputable def homQ : Rep.res π (Rep.defectQ B E) ⟶ Rep.defectQ (Rep.res π B) E' :=
  RepImage.map ((Rep.resFunctor π).map (Rep.preι B E)) (Rep.preι (Rep.res π B) E')
    (Rep.extInflF π B E E' φ) (Rep.extInflR π B E E' φ) (extInflF_comp_preι π B E E' φ)

theorem homQ_hom_apply_coe (y : Rep.res π (Rep.defectQ B E)) :
    ((homQ π B E E' φ).hom y : (ihom (Rep.relationModuleInt (Rep.res π B))).obj E') =
      (Rep.extInflR π B E E' φ).hom (show Rep.defectQ B E from y).1 := rfl

theorem homQ_comp_f :
    homQ π B E E' φ ≫ (Rep.homSeq₂ (Rep.res π B) E').f = (Rep.resFunctor π).map (Rep.homSeq₂ B E).f ≫ Rep.extInflR π B E E' φ :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

section Kummer

variable {p : ℕ} [Fact p.Prime] [Fintype B] (hB : ∀ b : B, p • b = 0) (hφ : ∀ e : E, ∃ e' : E', φ.hom e = p • e')

noncomputable def lamQ : Rep.res π ((ihom (Rep.relationModuleInt B)).obj E) ⟶ Rep.defectQ (Rep.res π B) E' :=
  liftToImage (Rep.preι (Rep.res π B) E') (Rep.extInflR π B E E' φ) (fun f =>
    (RepCokernel.π_hom_apply_eq_zero_iff _ _).1 (congrArg (fun ψ => ψ.hom f)
      (Rep.extInflR_comp_homSeqTwo_g_eq_zero_of_forall_exists_eq_smul π B E E' φ p hB hφ)))

theorem lamQ_comp_f : lamQ π B E E' φ hB hφ ≫ (Rep.homSeq₂ (Rep.res π B) E').f = Rep.extInflR π B E E' φ :=
  liftToImage_ι _ _ _

noncomputable def eta (x : groupCohomology ((ihom (Rep.relationModuleInt B)).obj E) 1) :
    groupCohomology (Rep.defectQ (Rep.res π B) E') 1 :=
  (groupCohomology.map π (lamQ π B E E' φ hB hφ) 1).hom x

theorem inf_eq_psi_eta (x : groupCohomology ((ihom (Rep.relationModuleInt B)).obj E) 1) :
    (groupCohomology.map π (Rep.extInflR π B E E' φ) 1).hom x =
      (groupCohomology.map (MonoidHom.id G') (Rep.homSeq₂ (Rep.res π B) E').f 1).hom (eta π B E E' φ hB hφ x) := by
  have h : groupCohomology.map π (Rep.extInflR π B E E' φ) 1 =
      groupCohomology.map π (lamQ π B E E' φ hB hφ) 1 ≫
        groupCohomology.map (MonoidHom.id G') (A := Rep.defectQ (Rep.res π B) E') (Rep.homSeq₂ (Rep.res π B) E').f 1 := by
    rw [← groupCohomology.map_comp]
    congr 1
  have h' := congrArg (fun ψ => (ModuleCat.Hom.hom ψ) x) h
  try simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'

end Kummer

end KD

namespace KD

open GroupCohomology

section naturality

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')

theorem inf_psi_eq_psi_homQ (η : groupCohomology (Rep.defectQ B E) 1) :
    (groupCohomology.map π (Rep.extInflR π B E E' φ) 1).hom
        ((groupCohomology.map (MonoidHom.id G) (Rep.homSeq₂ B E).f 1).hom η) =
      (groupCohomology.map (MonoidHom.id G') (Rep.homSeq₂ (Rep.res π B) E').f 1).hom
        ((groupCohomology.map π (homQ π B E E' φ) 1).hom η) := by
  have h1 := groupCohomology.map_comp (A := Rep.defectQ B E) (B := (ihom (Rep.relationModuleInt B)).obj E)
    (MonoidHom.id G) π (Rep.homSeq₂ B E).f (Rep.extInflR π B E E' φ) 1
  have h2 := groupCohomology.map_comp (A := Rep.defectQ B E) (B := Rep.defectQ (Rep.res π B) E')
    (C := (ihom (Rep.relationModuleInt (Rep.res π B))).obj E')
    π (MonoidHom.id G') (homQ π B E E' φ) (Rep.homSeq₂ (Rep.res π B) E').f 1
  have e : groupCohomology.map ((MonoidHom.id G).comp π)
      ((Rep.resFunctor π).map (Rep.homSeq₂ B E).f ≫ Rep.extInflR π B E E' φ) 1 =
      groupCohomology.map (π.comp (MonoidHom.id G'))
        ((Rep.resFunctor (MonoidHom.id G')).map (homQ π B E E' φ) ≫ (Rep.homSeq₂ (Rep.res π B) E').f) 1 := by
    change groupCohomology.map π ((Rep.resFunctor π).map (Rep.homSeq₂ B E).f ≫ Rep.extInflR π B E E' φ) 1 =
      groupCohomology.map π (homQ π B E E' φ ≫ (Rep.homSeq₂ (Rep.res π B) E').f) 1
    rw [homQ_comp_f]
    rfl
  have h := congrArg (fun ψ => (ModuleCat.Hom.hom ψ) η) (h1.symm.trans (e.trans h2))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

end naturality

section vanishing

variable {G : Type} [Group G] [Fintype G] (B E : Rep ℤ G)

theorem eq_zero_of_delta_eq_zero (η : groupCohomology (Rep.defectQ B E) 1)
    (h : (groupCohomology.δ (Rep.homSeqOne_shortExact B E) 1 2 rfl).hom η = 0) : η = 0 := by
  have hex := groupCohomology.mapShortComplex₃_exact (Rep.homSeqOne_shortExact B E) (i := 1) (j := 2) rfl
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex η h
  have hz : Limits.IsZero (groupCohomology ((ihom (Rep.free ℤ G B)).obj E) 1) :=
    Rep.isZero_tateCohomology_ihom_free B E 1
  have hy0 : y = 0 := by
    have e := hz.eq_of_src (𝟙 (groupCohomology ((ihom (Rep.free ℤ G B)).obj E) 1)) 0
    have := congrArg (fun ψ => (ModuleCat.Hom.hom ψ) y) e
    first | exact this | simpa using this | simpa +zetaDelta using this
  rw [← hy, hy0, map_zero]
  rfl

end vanishing

end KD

namespace KD

open GroupCohomology

section deltaNat

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')

theorem homB_comp_preCover :
    homB π B E E' φ ≫ Rep.preCover (Rep.res π B) E' = (Rep.resFunctor π).map (Rep.preCover B E) ≫ Rep.extInflF π B E E' φ := by
  change (Rep.resIhom π B E ≫ (ihom (Rep.res π B)).map φ) ≫ Rep.preHom (Rep.freeCover (Rep.res π B)) E' =
    (Rep.resFunctor π).map (Rep.preHom (Rep.freeCover B) E) ≫
      Rep.resIhom π (Rep.free ℤ G B) E ≫ Rep.preHom (Rep.freeResMap π B) (Rep.res π E) ≫ (ihom (Rep.free ℤ G' (Rep.res π B))).map φ
  rw [← Category.assoc ((Rep.resFunctor π).map _), resFunctor_map_preHom_comp_resIhom, Category.assoc, Category.assoc,
    ← Category.assoc (Rep.preHom ((Rep.resFunctor π).map (Rep.freeCover B)) (Rep.res π E)), Rep.preHom_comp,
    Rep.freeResMap_comp_resFunctor_map_freeCover, ihom_map_comp_preHom]

theorem extInflF_comp_toImage :
    Rep.extInflF π B E E' φ ≫ RepImage.toImage (Rep.preι (Rep.res π B) E') =
      (Rep.resFunctor π).map (RepImage.toImage (Rep.preι B E)) ≫ homQ π B E E' φ :=
  Rep.hom_ext (DFunLike.ext _ _ fun f => Subtype.ext
    (congrArg (fun ψ => ψ.hom f) (extInflF_comp_preι π B E E' φ)))

noncomputable def cochainsHom :
    (Rep.homSeq₁ B E).map (groupCohomology.cochainsFunctor ℤ G) ⟶
      (Rep.homSeq₁ (Rep.res π B) E').map (groupCohomology.cochainsFunctor ℤ G') :=
  ShortComplex.homMk (cochainsMap π (homB π B E E' φ)) (cochainsMap π (Rep.extInflF π B E E' φ))
    (cochainsMap π (homQ π B E E' φ))
    (by
      change cochainsMap π (homB π B E E' φ) ≫ cochainsMap (MonoidHom.id G') (Rep.preCover (Rep.res π B) E') =
        cochainsMap (MonoidHom.id G) (Rep.preCover B E) ≫ cochainsMap π (Rep.extInflF π B E E' φ)
      rw [← cochainsMap_comp, ← cochainsMap_comp]
      change cochainsMap π (homB π B E E' φ ≫ Rep.preCover (Rep.res π B) E') =
        cochainsMap π ((Rep.resFunctor π).map (Rep.preCover B E) ≫ Rep.extInflF π B E E' φ)
      rw [homB_comp_preCover])
    (by
      change cochainsMap π (Rep.extInflF π B E E' φ) ≫ cochainsMap (MonoidHom.id G') (RepImage.toImage (Rep.preι (Rep.res π B) E')) =
        cochainsMap (MonoidHom.id G) (RepImage.toImage (Rep.preι B E)) ≫ cochainsMap π (homQ π B E E' φ)
      rw [← cochainsMap_comp, ← cochainsMap_comp]
      change cochainsMap π (Rep.extInflF π B E E' φ ≫ RepImage.toImage (Rep.preι (Rep.res π B) E')) =
        cochainsMap π ((Rep.resFunctor π).map (RepImage.toImage (Rep.preι B E)) ≫ homQ π B E E' φ)
      rw [extInflF_comp_toImage])

theorem delta_homQ_eq_homB_delta (η : groupCohomology (Rep.defectQ B E) 1) :
    (groupCohomology.δ (Rep.homSeqOne_shortExact (Rep.res π B) E') 1 2 rfl).hom
        ((groupCohomology.map π (homQ π B E E' φ) 1).hom η) =
      (groupCohomology.map π (homB π B E E' φ) 2).hom
        ((groupCohomology.δ (Rep.homSeqOne_shortExact B E) 1 2 rfl).hom η) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (cochainsHom π B E E' φ)
    (groupCohomology.map_cochainsFunctor_shortExact (Rep.homSeqOne_shortExact B E))
    (groupCohomology.map_cochainsFunctor_shortExact (Rep.homSeqOne_shortExact (Rep.res π B) E')) 1 2 rfl
  have h' := congrArg (fun ψ => (ModuleCat.Hom.hom ψ) η) h
  try simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'.symm

end deltaNat

end KD

namespace KD

open GroupCohomology

section transGeneral

universe u

variable {k G G' G'' : Type u} [CommRing k] [Group G] [Group G'] [Group G''] (π : G' →* G) (π' : G'' →* G')

theorem freeResMap_comp (B : Rep.{u} k G) :
    Rep.freeResMap (π.comp π') B = Rep.freeResMap π' (Rep.res π B) ≫ (Rep.resFunctor π').map (Rep.freeResMap π B) :=
  Rep.free_ext k G'' _ _ _ (fun b => by simp [Rep.freeResMap, Rep.resMap])

theorem resIhom_comp (R X : Rep.{u} k G) :
    Rep.resIhom (π.comp π') R X = (Rep.resFunctor π').map (Rep.resIhom π R X) ≫ Rep.resIhom π' (Rep.res π R) (Rep.res π X) :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

end transGeneral

section trans

variable {G G' G'' : Type} [Group G] [Group G'] [Group G''] (π : G' →* G) (π' : G'' →* G')
  (B E : Rep ℤ G) (E' : Rep ℤ G') (E'' : Rep ℤ G'') (φ : Rep.res π E ⟶ E') (φ' : Rep.res π' E' ⟶ E'')

theorem resMap_comp :
    Rep.relationModuleInt.resMap (π.comp π') B =
      Rep.relationModuleInt.resMap π' (Rep.res π B) ≫ (Rep.resFunctor π').map (Rep.relationModuleInt.resMap π B) :=
  Rep.hom_ext (DFunLike.ext _ _ fun y => Subtype.ext
    (congrArg (fun ψ => ψ.hom ((Rep.relationModuleInt.ι (Rep.res (π.comp π') B)).hom y)) (freeResMap_comp π π' B)))

attribute [local instance 10000] Rep.hV1 Rep.hV2 in

theorem extInflR_comp :
    Rep.extInflR (π.comp π') B E E'' ((Rep.resFunctor π').map φ ≫ φ') =
      (Rep.resFunctor π').map (Rep.extInflR π B E E' φ) ≫ Rep.extInflR π' (Rep.res π B) E' E'' φ' := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun f => LinearMap.ext fun y => ?_
  change LinearMap.toAddMonoidHom ((Rep.extInflR (π.comp π') B E E'' ((Rep.resFunctor π').map φ ≫ φ')).hom f) y =
    LinearMap.toAddMonoidHom ((Rep.extInflR π' (Rep.res π B) E' E'' φ').hom ((Rep.extInflR π B E E' φ).hom f)) y
  rw [extInflR_hom_apply, extInflR_hom_apply, extInflR_hom_apply]
  change φ'.hom (φ.hom _) = φ'.hom (φ.hom _)
  congr 2
  exact congrArg (fun ψ => LinearMap.toAddMonoidHom (show (ihom (Rep.relationModuleInt B)).obj E from f)
    (show Rep.relationModuleInt B from ψ.hom y)) (resMap_comp π π' B)

theorem inf_comp (x : groupCohomology ((ihom (Rep.relationModuleInt B)).obj E) 1) :
    (groupCohomology.map (π.comp π') (Rep.extInflR (π.comp π') B E E'' ((Rep.resFunctor π').map φ ≫ φ')) 1).hom x =
      (groupCohomology.map π' (Rep.extInflR π' (Rep.res π B) E' E'' φ') 1).hom
        ((groupCohomology.map π (Rep.extInflR π B E E' φ) 1).hom x) := by
  have h := groupCohomology.map_comp π π' (Rep.extInflR π B E E' φ) (Rep.extInflR π' (Rep.res π B) E' E'' φ') 1
  rw [← extInflR_comp] at h
  have h' := congrArg (fun ψ => (ModuleCat.Hom.hom ψ) x) h
  try simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'

end trans

end KD

namespace KDC

open NumberField.SUnits

lemma finite_placesAbove (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Finite (placesAbove ℚ ↥F Sℚ) := by
  have hfib : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      {w : HeightOneSpectrum (𝓞 ↥F) | w.under (𝓞 ℚ) = v}.Finite := by
    intro v
    haveI := v.isMaximal
    have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 ↥F) => w.asIdeal)
        ((fun w : HeightOneSpectrum (𝓞 ↥F) => w.asIdeal) ⁻¹' (v.asIdeal.primesOver (𝓞 ↥F))) :=
      fun _ _ _ _ h => HeightOneSpectrum.ext h
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 ↥F)).preimage hinj).subset fun w hw => ?_
    have hw' : w.under (𝓞 ℚ) = v := hw
    exact ⟨w.isPrime, ⟨by rw [← hw']; rfl⟩⟩
  have hsub : placesAbove ℚ ↥F Sℚ ⊆ ⋃ v ∈ (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))),
      {w : HeightOneSpectrum (𝓞 ↥F) | w.under (𝓞 ℚ) = v} := fun w hw =>
    Set.mem_biUnion ((mem_placesAbove ℚ ↥F Sℚ w).1 hw) rfl
  exact ((Sℚ.finite_toSet.biUnion fun v _ => hfib v).subset hsub).to_subtype

lemma exists_prime_natCast_mem (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
  haveI := w.isMaximal
  haveI : Finite (𝓞 ↥F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 ↥F ⧸ w.asIdeal)
  refine ⟨q, CharP.char_is_prime (𝓞 ↥F ⧸ w.asIdeal) q, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ q

lemma exists_prime_not_mem (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (hw : w ∉ placesAbove ℚ ↥F Sℚ) :
    ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
  obtain ⟨q, hq, hqw⟩ := exists_prime_natCast_mem F w
  refine ⟨⟨q, hq⟩, fun hqS => hw ?_, hqw⟩
  rw [mem_placesAbove, ← Finset.mem_coe, hSℚ, NumberField.mem_placesOverPrimes_iff]
  refine ⟨⟨q, hq⟩, hqS, ?_⟩
  change algebraMap (𝓞 ℚ) (𝓞 ↥F) ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  rwa [map_natCast]

lemma mem_sUnits_of_forall_mem_and_inv_mem (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] (x : (↥F)ˣ)
    (hx : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((x : ↥F) : AlgebraicClosure ℚ) ∈ A ∧ ((x : ↥F) : AlgebraicClosure ℚ)⁻¹ ∈ A) :
    x ∈ sUnits ℚ ↥F Sℚ := by
  rw [NumberField.SUnits.sUnits_eq_unit]
  simp only [Set.unit]
  intro w hw
  obtain ⟨q, hqS, hqw⟩ := exists_prime_not_mem S Sℚ hSℚ F w hw
  obtain ⟨B, hB⟩ := NumberField.exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one F w
  have hq0 : ((q : ℕ) : ↥F) ≠ 0 := by exact_mod_cast q.2.ne_zero

  have hvq : w.valuation ↥F ((q : ℕ) : ↥F) < 1 := by
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥F) w ((q : ℕ) : 𝓞 ↥F)).2 hqw
    simpa using h

  have hBq : B.LiesOverPrime (q : ℕ) := by
    change ((q : ℕ) : AlgebraicClosure ℚ) ∈ B.nonunits
    rw [ValuationSubring.mem_nonunits_iff]
    have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ B := by
      exact (hB ((q : ℕ) : ↥F)).2 hvq.le
    refine lt_of_le_of_ne ((B.valuation_le_one_iff _).2 hmem) fun h1 => ?_
    have hinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ B := by
      apply B.mem_of_valuation_le_one
      rw [map_inv₀, h1, inv_one]
    have hinv' : w.valuation ↥F ((q : ℕ) : ↥F)⁻¹ ≤ 1 := by
      refine (hB _).1 ?_
      simpa using hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hq0))] at hinv'
    exact not_lt.2 hinv' hvq

  obtain ⟨h1, h2⟩ := hx q hqS B hBq
  have hle : w.valuation ↥F (x : ↥F) ≤ 1 := (hB _).1 h1
  have hle' : w.valuation ↥F (x : ↥F)⁻¹ ≤ 1 := (hB _).1 (by simpa using h2)
  have hx0 : w.valuation ↥F (x : ↥F) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero x)
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hx0)] at hle'
  exact le_antisymm hle hle'

theorem map_int_smul' {V W : Type} [AddCommGroup V] [AddCommGroup W] {mV : Module ℤ V} {mW : Module ℤ W}
    (ψ : V →+ W) (c : ℤ) (x : V) :
    ψ (@HSMul.hSMul ℤ V V (@instHSMul ℤ V ((@Module.toDistribMulAction ℤ V _ _ mV).toDistribSMul.toSMul)) c x) =
    @HSMul.hSMul ℤ W W (@instHSMul ℤ W ((@Module.toDistribMulAction ℤ W _ _ mW).toDistribSMul.toSMul)) c (ψ x) := by
  have e1 : mV = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  have e2 : mW = AddCommGroup.toIntModule W := Subsingleton.elim _ _
  subst e1
  subst e2
  exact map_zsmul ψ c x

section tower

variable (L L' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : L ≤ L')

@[reducible] noncomputable def towerAlgebra : Algebra ↥L ↥L' := (IntermediateField.inclusion h).toRingHom.toAlgebra

theorem towerAlgebra_isScalarTower : letI := towerAlgebra L L' h; IsScalarTower ℚ ↥L ↥L' := by
  letI := towerAlgebra L L' h
  exact IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion h).commutes x).symm

noncomputable def levelHom [Normal ℚ ↥L] : (↥L' ≃ₐ[ℚ] ↥L') →* (↥L ≃ₐ[ℚ] ↥L) := by
  letI := towerAlgebra L L' h
  haveI := towerAlgebra_isScalarTower L L' h
  exact AlgEquiv.restrictNormalHom ↥L

theorem levelHom_apply_coe [Normal ℚ ↥L] (σ : ↥L' ≃ₐ[ℚ] ↥L') (x : ↥L) :
    ((levelHom L L' h σ x : ↥L) : AlgebraicClosure ℚ) =
      ((σ (IntermediateField.inclusion h x) : ↥L') : AlgebraicClosure ℚ) := by
  letI := towerAlgebra L L' h
  haveI := towerAlgebra_isScalarTower L L' h
  have hc := AlgEquiv.restrictNormal_commutes σ ↥L x
  exact congrArg (fun y : ↥L' => (y : AlgebraicClosure ℚ)) hc

theorem levelHom_restrictNormalHom [Normal ℚ ↥L] [Normal ℚ ↥L'] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    levelHom L L' h (AlgEquiv.restrictNormalHom ↥L' σ) = AlgEquiv.restrictNormalHom ↥L σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [levelHom_apply_coe]
  have h1 := AlgEquiv.restrictNormal_commutes σ ↥L' (IntermediateField.inclusion h x)
  have h2 := AlgEquiv.restrictNormal_commutes σ ↥L x
  exact h1.trans h2.symm

theorem map_inclusion_mem_sUnits (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes)) [NumberField ↥L] [NumberField ↥L'] (u : (↥L)ˣ) (hu : u ∈ sUnits ℚ ↥L Sℚ) :
    Units.map (IntermediateField.inclusion h : ↥L →* ↥L') u ∈ sUnits ℚ ↥L' Sℚ := by
  apply mem_sUnits_of_forall_mem_and_inv_mem S Sℚ hSℚ L'
  intro q hq A hA
  exact NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime S Sℚ hSℚ L u hu q hq A hA

noncomputable def inclAdd (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes)) [NumberField ↥L] [NumberField ↥L'] : sUnitsRep ℚ ↥L Sℚ →+ sUnitsRep ℚ ↥L' Sℚ where
  toFun e := ⟨Additive.ofMul (Units.map (IntermediateField.inclusion h : ↥L →* ↥L') (val ℚ ↥L Sℚ e)),
    map_inclusion_mem_sUnits L L' h S Sℚ hSℚ _ (val_mem ℚ ↥L Sℚ e)⟩
  map_zero' := Subtype.ext (by simp; rfl)
  map_add' x y := Subtype.ext (by simp; rfl)

theorem val_inclAdd (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes)) [NumberField ↥L] [NumberField ↥L'] (e : sUnitsRep ℚ ↥L Sℚ) :
    val ℚ ↥L' Sℚ (inclAdd L L' h S Sℚ hSℚ e) = Units.map (IntermediateField.inclusion h : ↥L →* ↥L') (val ℚ ↥L Sℚ e) := rfl

noncomputable def sUnitsIncl (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes)) [NumberField ↥L] [NumberField ↥L'] [Normal ℚ ↥L] :
    Rep.res (levelHom L L' h) (sUnitsRep ℚ ↥L Sℚ) ⟶ sUnitsRep ℚ ↥L' Sℚ :=
  Rep.ofHom ⟨{ toFun := fun e => inclAdd L L' h S Sℚ hSℚ e
               map_add' := fun x y => (inclAdd L L' h S Sℚ hSℚ).map_add x y
               map_smul' := fun c x => map_int_smul' (inclAdd L L' h S Sℚ hSℚ) c x },
    fun σ => LinearMap.ext fun e => by
      apply Subtype.ext
      apply congrArg Additive.ofMul
      apply Units.ext
      apply Subtype.ext
      change (((IntermediateField.inclusion h) ((levelHom L L' h σ) (val ℚ ↥L Sℚ e : ↥L)) : ↥L') : AlgebraicClosure ℚ) =
        ((σ (IntermediateField.inclusion h (val ℚ ↥L Sℚ e : ↥L)) : ↥L') : AlgebraicClosure ℚ)
      exact levelHom_apply_coe L L' h σ _⟩

theorem val_sUnitsIncl (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes)) [NumberField ↥L] [NumberField ↥L'] [Normal ℚ ↥L] (e : sUnitsRep ℚ ↥L Sℚ) :
    val ℚ ↥L' Sℚ ((sUnitsIncl L L' h S Sℚ hSℚ).hom e) =
      Units.map (IntermediateField.inclusion h : ↥L →* ↥L') (val ℚ ↥L Sℚ e) := rfl

theorem map_val_sUnitsIncl (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes)) [NumberField ↥L] [NumberField ↥L'] [Normal ℚ ↥L] (e : sUnitsRep ℚ ↥L Sℚ) :
    Units.map (algebraMap ↥L' (AlgebraicClosure ℚ) : ↥L' →* AlgebraicClosure ℚ) (val ℚ ↥L' Sℚ ((sUnitsIncl L L' h S Sℚ hSℚ).hom e)) =
      Units.map (algebraMap ↥L (AlgebraicClosure ℚ) : ↥L →* AlgebraicClosure ℚ) (val ℚ ↥L Sℚ e) :=
  Units.ext rfl

end tower

section pdiv

variable {p : ℕ} [Fact p.Prime] (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (F₁ F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [NumberField ↥F₃]
  {π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁)}

theorem ιE_injective (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (ιE : sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (val ℚ ↥F Sℚ x)) :
    Function.Injective ιE := fun a b hab => by
  have h := congrArg Additive.toMul hab
  rw [hιE, hιE] at h
  have hv : val ℚ ↥F Sℚ a = val ℚ ↥F Sℚ b :=
    Units.ext ((algebraMap ↥F (AlgebraicClosure ℚ)).injective (congrArg (fun u : (AlgebraicClosure ℚ)ˣ => (u : AlgebraicClosure ℚ)) h))
  exact Subtype.ext (congrArg Additive.ofMul hv)

theorem forall_exists_eq_nsmul
    (ιE₁ : sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₁ : ∀ x, Additive.toMul (ιE₁ x) = Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (val ℚ ↥F₁ Sℚ x))
    (ιE₃ : sUnitsRep ℚ ↥F₃ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₃ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (val ℚ ↥F₃ Sℚ x))
    (jE : Rep.res π (sUnitsRep ℚ ↥F₁ Sℚ) ⟶ sUnitsRep ℚ ↥F₃ Sℚ) (hjE : ∀ x, ιE₃ (jE.hom x) = ιE₁ x)
    (hK : ∀ e : sUnitsRep ℚ ↥F₁ Sℚ, ∃ e' : sUnitsRep ℚ ↥F₃ Sℚ,
      Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (val ℚ ↥F₁ Sℚ e) =
        (Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (val ℚ ↥F₃ Sℚ e')) ^ p) :
    ∀ e : sUnitsRep ℚ ↥F₁ Sℚ, ∃ e' : sUnitsRep ℚ ↥F₃ Sℚ, jE.hom e = p • e' := by
  intro e
  obtain ⟨e', he'⟩ := hK e
  refine ⟨e', ιE_injective Sℚ F₃ ιE₃ hιE₃ (Additive.toMul.injective ?_)⟩
  rw [hjE, map_nsmul, toMul_nsmul, hιE₁, hιE₃, he']

end pdiv

end KDC

namespace KD2

section ihomEl

variable {G : Type} [Group G] (B E : Rep ℤ G)

attribute [local instance 10000] Rep.hV1 Rep.hV2

theorem ihom_ext {c c' : (ihom B).obj E}
    (h : ∀ b, LinearMap.toAddMonoidHom c b = LinearMap.toAddMonoidHom c' b) : c = c' :=
  LinearMap.ext h

theorem ihom_add_apply (c c' : (ihom B).obj E) (b : B) :
    LinearMap.toAddMonoidHom (c + c') b = LinearMap.toAddMonoidHom c b + LinearMap.toAddMonoidHom c' b := rfl

theorem ihom_rho_apply (g : G) (c : (ihom B).obj E) (b : B) :
    LinearMap.toAddMonoidHom (((ihom B).obj E).ρ g c) b = E.ρ g (LinearMap.toAddMonoidHom c (B.ρ g⁻¹ b)) := by
  erw [Rep.ihom_obj_ρ_apply]; rfl

noncomputable def mkIhom (f : B →+ E) : (ihom B).obj E where
  toFun := f
  map_add' := f.map_add
  map_smul' n b := by simpa using map_intCast_smul f ℤ ℤ n b

theorem mkIhom_apply (f : B →+ E) (b : B) : LinearMap.toAddMonoidHom (mkIhom B E f) b = f b := rfl

end ihomEl

section primitive

variable {Γ D D' : Type} [Group Γ] [Group D] [Group D'] (q : Γ →* D') (hq : Function.Surjective q) (π : D' →* D)
  (B E : Rep ℤ D) (E' : Rep ℤ D') (jE : Rep.res π E ⟶ E')
  {A : Rep ℤ Γ} (ι : E →+ A) (ι' : E' →+ A) (hιj : ∀ e, ι' (jE.hom e) = ι e) (hι' : Function.Injective ι')
  (hι'eq : ∀ (γ : Γ) (e : E'), ι' (E'.ρ (q γ) e) = A.ρ γ (ι' e))
  {p : ℕ} {M : Rep (ZMod p) Γ} (κ : B →+ M →+ A)
  (hκeq : ∀ (γ : Γ) (b : B) (m : M), κ (B.ρ (π (q γ)) b) (M.ρ γ m) = A.ρ γ (κ b m))
  (hval : ∀ (b₀ : B) (m : M), ∃ e : E', ι' e = κ b₀ m)
  (b : Γ → M) (hb : ∀ γ s, q s = 1 → b (γ * s) = b γ)

private noncomputable abbrev _root_.KD2.homB : Rep.res π ((ihom B).obj E) ⟶ (ihom (Rep.res π B)).obj E' := Rep.resIhom π B E ≫ (ihom (Rep.res π B)).map jE

p2m_export "KD2" "homB"
theorem homB_apply (ψ : (ihom B).obj E) (b₀ : B) :
    LinearMap.toAddMonoidHom ((homB π B E E' jE).hom ψ) b₀ = jE.hom (LinearMap.toAddMonoidHom ψ b₀) := rfl

noncomputable def sec : D' → Γ := Function.surjInv hq

theorem q_sec (g : D') : q (sec q hq g) = g := Function.surjInv_eq hq g

include hb in
theorem b_sec_mul (g₁ g₂ : D') : b (sec q hq (g₁ * g₂)) = b (sec q hq g₁ * sec q hq g₂) := by
  have h : q ((sec q hq g₁ * sec q hq g₂)⁻¹ * sec q hq (g₁ * g₂)) = 1 := by
    rw [map_mul, map_inv, map_mul, q_sec, q_sec, q_sec, inv_mul_cancel]
  have := hb (sec q hq g₁ * sec q hq g₂) _ h
  rw [mul_inv_cancel_left] at this
  exact this

noncomputable def readFun (m : M) (b₀ : B) : E' := (hval b₀ m).choose

theorem ι'_readFun (m : M) (b₀ : B) : ι' (readFun B E' ι' κ hval m b₀) = κ b₀ m := (hval b₀ m).choose_spec

include hι' in
theorem readFun_add (m : M) (b₁ b₂ : B) :
    readFun B E' ι' κ hval m (b₁ + b₂) = readFun B E' ι' κ hval m b₁ + readFun B E' ι' κ hval m b₂ := by
  apply hι'
  rw [map_add, ι'_readFun, ι'_readFun, ι'_readFun, map_add, AddMonoidHom.add_apply]

noncomputable def readAdd (m : M) : B →+ E' where
  toFun := readFun B E' ι' κ hval m
  map_zero' := by apply hι'; rw [ι'_readFun, map_zero, AddMonoidHom.zero_apply, map_zero]
  map_add' := readFun_add B E' ι' hι' κ hval m

noncomputable def β (g : D') : (ihom (Rep.res π B)).obj E' := mkIhom (Rep.res π B) E' (readAdd B E' ι' hι' κ hval (b (sec q hq g)))

theorem ι'_β_apply (g : D') (b₀ : B) : ι' (LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b g) b₀) = κ b₀ (b (sec q hq g)) := by
  change ι' (readFun B E' ι' κ hval (b (sec q hq g)) b₀) = _
  exact ι'_readFun B E' ι' κ hval _ b₀

include hιj hι'eq hκeq hb in

theorem d₁₂_β_eq (c : D × D → (ihom B).obj E)
    (hbm : ∀ (γ₁ γ₂ : Γ) (b₀ : B), κ b₀ ((d₁₂ M).hom b (γ₁, γ₂)) =
      ι (LinearMap.toAddMonoidHom (c (π (q γ₁), π (q γ₂))) b₀)) :
    (d₁₂ ((ihom (Rep.res π B)).obj E')).hom (β q hq π B E' ι' hι' κ hval b) =
      fun g : D' × D' => (homB π B E E' jE).hom (c (π g.1, π g.2)) := by
  funext g
  obtain ⟨g₁, g₂⟩ := g
  apply ihom_ext
  intro b₀
  apply hι'
  rw [d₁₂_hom_apply]
  change ι' (LinearMap.toAddMonoidHom ((((ihom (Rep.res π B)).obj E').ρ g₁ (β q hq π B E' ι' hι' κ hval b g₂) -
      β q hq π B E' ι' hι' κ hval b (g₁ * g₂) + β q hq π B E' ι' hι' κ hval b g₁)) b₀) =
    ι' (LinearMap.toAddMonoidHom ((homB π B E E' jE).hom (c (π g₁, π g₂))) b₀)
  rw [homB_apply, hιj]

  have e1 : LinearMap.toAddMonoidHom ((((ihom (Rep.res π B)).obj E').ρ g₁ (β q hq π B E' ι' hι' κ hval b g₂) -
      β q hq π B E' ι' hι' κ hval b (g₁ * g₂) + β q hq π B E' ι' hι' κ hval b g₁)) b₀ =
      E'.ρ g₁ (LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b g₂) (B.ρ (π g₁⁻¹) b₀)) -
        LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b (g₁ * g₂)) b₀ +
        LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b g₁) b₀ := by
    change LinearMap.toAddMonoidHom (((ihom (Rep.res π B)).obj E').ρ g₁ (β q hq π B E' ι' hι' κ hval b g₂)) b₀ -
        LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b (g₁ * g₂)) b₀ +
        LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b g₁) b₀ = _
    rw [ihom_rho_apply]
    rfl

  have key : ι' (E'.ρ g₁ (LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b g₂) (B.ρ (π g₁⁻¹) b₀))) =
      κ b₀ (M.ρ (sec q hq g₁) (b (sec q hq g₂))) := by
    have h1 := hι'eq (sec q hq g₁) (LinearMap.toAddMonoidHom (β q hq π B E' ι' hι' κ hval b g₂) (B.ρ (π g₁⁻¹) b₀))
    rw [q_sec] at h1
    have e2 : B.ρ (π g₁) (B.ρ (π g₁⁻¹) b₀) = b₀ := by
      show (B.ρ (π g₁) * B.ρ (π g₁⁻¹)) b₀ = b₀
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
      rfl
    rw [h1, ι'_β_apply, ← hκeq (sec q hq g₁) (B.ρ (π g₁⁻¹) b₀) (b (sec q hq g₂)), q_sec, e2]
  have hbm' := hbm (sec q hq g₁) (sec q hq g₂) b₀
  rw [q_sec, q_sec] at hbm'
  rw [e1, map_add, map_sub, key, ι'_β_apply, ι'_β_apply, b_sec_mul q hq b hb g₁ g₂, ← hbm', d₁₂_hom_apply, map_add, map_sub]

include hq hι' hval hιj hι'eq hκeq hb in

theorem map_H2π_eq_zero (c : cocycles₂ ((ihom B).obj E))
    (hbm : ∀ (γ₁ γ₂ : Γ) (b₀ : B), κ b₀ ((d₁₂ M).hom b (γ₁, γ₂)) =
      ι (LinearMap.toAddMonoidHom ((c : D × D → (ihom B).obj E) (π (q γ₁), π (q γ₂))) b₀)) :
    (groupCohomology.map π (homB π B E E' jE) 2).hom ((H2π _).hom c) = 0 := by
  erw [H2π_comp_map_apply, H2π_eq_zero_iff]
  exact ⟨β q hq π B E' ι' hι' κ hval b, d₁₂_β_eq q hq π B E E' jE ι ι' hιj hι' hι'eq κ hκeq hval b hb c hbm⟩

end primitive

end KD2

namespace KD2

section sunits

variable {Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))} (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
  (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥L Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥L (AlgebraicClosure ℚ) : ↥L →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥L Sℚ x))

include hιE

theorem iotaE_injective : Function.Injective ιE := by
  intro x y h
  have h' : ((Additive.toMul (ιE x) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = Additive.toMul (ιE y) := by rw [h]
  rw [hιE, hιE] at h'
  have h'' : NumberField.SUnits.val ℚ ↥L Sℚ x = NumberField.SUnits.val ℚ ↥L Sℚ y :=
    Units.ext ((algebraMap ↥L (AlgebraicClosure ℚ)).injective h')
  exact Subtype.ext (congrArg Additive.ofMul h'')

theorem iotaE_rho [IsGalois ℚ ↥L] (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : (NumberField.SUnits.sUnitsRep ℚ ↥L Sℚ)) :
    ιE ((NumberField.SUnits.sUnitsRep ℚ ↥L Sℚ).ρ (AlgEquiv.restrictNormalHom ↥L γ) x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (ιE x) := by
  change _ = (Rep.ofMulDistribMulAction _ (AlgebraicClosure ℚ)ˣ).ρ γ (ιE x)
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
  apply Additive.toMul.injective
  rw [toMul_ofMul, hιE, hιE]
  apply Units.ext
  change algebraMap ↥L (AlgebraicClosure ℚ) ((AlgEquiv.restrictNormalHom ↥L γ) (NumberField.SUnits.val ℚ ↥L Sℚ x : ↥L)) =
    γ (algebraMap ↥L (AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥L Sℚ x : ↥L))
  exact AlgEquiv.restrictNormal_commutes γ ↥L _

omit [NumberField ↥L] hιE in
theorem restrictNormalHom_eq_one_of_mem [IsGalois ℚ ↥L] (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs : s ∈ L.fixingSubgroup) :
    AlgEquiv.restrictNormalHom ↥L s = 1 := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap ↥L (AlgebraicClosure ℚ)).injective
  rw [show AlgEquiv.restrictNormalHom ↥L s = s.restrictNormal ↥L from rfl, AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs x.1 x.2

omit [NumberField ↥L] hιE in

theorem mem_fixingSubgroup_of_restrictNormalHom_eq_one [IsGalois ℚ ↥L] (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hs : AlgEquiv.restrictNormalHom ↥L s = 1) : s ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro a ha
  have h := AlgEquiv.restrictNormal_commutes s ↥L ⟨a, ha⟩
  rw [show s.restrictNormal ↥L = AlgEquiv.restrictNormalHom ↥L s from rfl, hs, AlgEquiv.one_apply] at h
  exact h.symm

end sunits

theorem relationModuleInt_ι_injective {G : Type} [Group G] (B : Rep ℤ G) : Function.Injective (Rep.relationModuleInt.ι B).hom :=
  fun _ _ h => Subtype.ext h

theorem exact_ι_freeCover {G : Type} [Group G] (B : Rep ℤ G) : Function.Exact (Rep.relationModuleInt.ι B).hom (Rep.freeCover B).hom := by
  intro y
  constructor
  · intro hy; exact ⟨(⟨y, hy⟩ : Rep.relationModule B), rfl⟩
  · rintro ⟨x, rfl⟩; exact x.2

theorem freeCover_surjective {G : Type} [Group G] (B : Rep ℤ G) : Function.Surjective (Rep.freeCover B).hom := by
  intro b
  refine ⟨Finsupp.single b (MonoidAlgebra.single 1 1), ?_⟩
  simp [Rep.freeCover]
  exact (int_smul_eq_zsmul B.hV2 1 b).trans (one_zsmul b)

scoped instance moduleFinite_free {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Finite B] : Module.Finite ℤ (Rep.free ℤ G B) :=
  Module.Finite.finsupp

theorem ι_comp_freeResMap {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B : Rep ℤ G) :
    Rep.relationModuleInt.ι (Rep.res π B) ≫ Rep.freeResMap π B =
      Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map (Rep.relationModuleInt.ι B) :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

section reading

variable {Γ D : Type} [Group Γ] [Group D] (q' : Γ →* D) (B X : Rep ℤ D)
  {A : Rep ℤ Γ} (ι : X →+ A) (hιeq : ∀ (γ : Γ) (x : X), ι (X.ρ (q' γ) x) = A.ρ γ (ι x))
  {p : ℕ} {M : Rep (ZMod p) Γ} (κ : B →+ M →+ A)
  (hκeq : ∀ (γ : Γ) (b : B) (m : M), κ (B.ρ (q' γ) b) (M.ρ γ m) = A.ρ γ (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

noncomputable def mRead (c : D × D → (ihom B).obj X) (γ : Γ × Γ) : M :=
  (hκ (ι.comp (LinearMap.toAddMonoidHom (c (q' γ.1, q' γ.2))))).exists.choose

theorem κ_mRead (c : D × D → (ihom B).obj X) (γ₁ γ₂ : Γ) (b : B) :
    κ b (mRead q' B X ι κ hκ c (γ₁, γ₂)) = ι (LinearMap.toAddMonoidHom (c (q' γ₁, q' γ₂)) b) :=
  (hκ (ι.comp (LinearMap.toAddMonoidHom (c (q' γ₁, q' γ₂))))).exists.choose_spec b

include hκ in
theorem κ_inj {m m' : M} (h : ∀ b, κ b m = κ b m') : m = m' :=
  (hκ (κ.flip m')).unique h (fun _ => rfl)

include hιeq hκeq in
theorem mRead_mem_cocycles₂ (c : cocycles₂ ((ihom B).obj X)) : mRead q' B X ι κ hκ c ∈ cocycles₂ M := by
  rw [mem_cocycles₂_iff]
  intro γ₁ γ₂ γ₃
  apply κ_inj B κ hκ
  intro b
  have hC := (mem_cocycles₂_iff (c : D × D → (ihom B).obj X)).1 c.2 (q' γ₁) (q' γ₂) (q' γ₃)
  have hCb := congrArg (fun y : (ihom B).obj X => ι (LinearMap.toAddMonoidHom y b)) hC
  rw [ihom_add_apply, ihom_add_apply, ihom_rho_apply, map_add, map_add, hιeq] at hCb

  have hρ : ∀ m : M, κ b (M.ρ γ₁ m) = A.ρ γ₁ (κ (B.ρ (q' γ₁)⁻¹ b) m) := by
    intro m
    rw [← hκeq γ₁ (B.ρ (q' γ₁)⁻¹ b) m]
    congr 2
    symm
    show (B.ρ (q' γ₁) * B.ρ (q' γ₁)⁻¹) b = b
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  rw [map_add, map_add, κ_mRead, κ_mRead, hρ, κ_mRead, κ_mRead]
  rw [← map_mul q', ← map_mul q'] at hCb
  exact hCb

end reading

set_option maxHeartbeats 6400000 in

theorem primitive_vanishes
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S)
    (hFM : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m)
    (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (ιE₁ : (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₁ : ∀ x, Additive.toMul (ιE₁ x) = Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ x))
    (hμ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ), ιE₁ e = Additive.ofMul u)
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    {Λ₁ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →+ continuousH2S S M}
    (hΛ₁ : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F₁) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE₁ κ Λ₁)

    (F₂' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₂'] [IsGalois ℚ ↥F₂'] (h₁₂ : F₁ ≤ F₂') (hF₂' : F₂'.IsUnramifiedOutside S)
    (π₁₂ : (↥F₂' ≃ₐ[ℚ] ↥F₂') →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
    (hπ₁₂ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π₁₂ (AlgEquiv.restrictNormalHom ↥F₂' σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
    (ιE₂ : (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₂ : ∀ x, Additive.toMul (ιE₂ x) = Units.map (algebraMap ↥F₂' (AlgebraicClosure ℚ) : ↥F₂' →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₂' Sℚ x))
    (jE₁₂ : Rep.res π₁₂ (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) ⟶ (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)) (hjE₁₂ : ∀ e, ιE₂ (jE₁₂.hom e) = ιE₁ e)
    (hdiv : ∀ e : (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ), ∃ e' : (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ), jE₁₂.hom e = p • e')

    (x : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) (hx : Λ₁ x = 0)
    (η : groupCohomology (Rep.defectQ (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)) 1)
    (hη : (groupCohomology.map π₁₂ (Rep.extInflR π₁₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) jE₁₂) 1).hom x =
      (groupCohomology.map (MonoidHom.id _) (Rep.homSeq₂ (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)).f 1).hom η) :
    ∃ Fb : IntermediateField ℚ (AlgebraicClosure ℚ), Fb.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] [IsGalois ℚ ↥F₃] (_ : F₂' ≤ F₃) (_ : Fb ≤ F₃)
        (π₂₃ : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₂' ≃ₐ[ℚ] ↥F₂'))
        (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π₂₃ (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₂' σ)
        (ιE₃ : (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
        (_ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ x))
        (jE₂₃ : Rep.res π₂₃ (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) ⟶ (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ)) (_ : ∀ e, ιE₃ (jE₂₃.hom e) = ιE₂ e),
        (groupCohomology.map π₂₃ (homB π₂₃ (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ) jE₂₃) 2).hom
          ((groupCohomology.δ (Rep.homSeqOne_shortExact (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)) 1 2 rfl).hom η) = 0 := by
  classical
  haveI : Fintype (↥F₂' ≃ₐ[ℚ] ↥F₂') := Fintype.ofFinite _
  have hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hAC : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI hNormal : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

  have hκeq₂ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : (Rep.res π₁₂ B)) (m : M),
      (show (Rep.res π₁₂ B) →+ M →+ Additive (AlgebraicClosure ℚ)ˣ from κ) ((Rep.res π₁₂ B).ρ (AlgEquiv.restrictNormalHom ↥F₂' γ) b) (M.ρ γ m) =
        (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ ((show (Rep.res π₁₂ B) →+ M →+ Additive (AlgebraicClosure ℚ)ˣ from κ) b m) := by
    intro γ b m
    change κ (B.ρ (π₁₂ (AlgEquiv.restrictNormalHom ↥F₂' γ)) b) (M.ρ γ m) = _
    rw [hπ₁₂]
    exact hκeq γ b m

  obtain ⟨Λ₂, hΛ₂⟩ := groupCohomology.exists_isGlobalBridge2 S (AlgEquiv.restrictNormalHom ↥F₂')
    ⟨F₂', hF₂', fun s hs => restrictNormalHom_eq_one_of_mem F₂' s hs⟩
    (Rep.relationModuleInt.ι (Rep.res π₁₂ B)) (Rep.freeCover (Rep.res π₁₂ B)) (exact_ι_freeCover (Rep.res π₁₂ B)) (freeCover_surjective (Rep.res π₁₂ B))
    (X := (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)) (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
    ιE₂ (iotaE_injective F₂' ιE₂ hιE₂) (iotaE_rho F₂' ιE₂ hιE₂)
    (p := p) (M := M) (show (Rep.res π₁₂ B) →+ M →+ Additive (AlgebraicClosure ℚ)ˣ from κ) hκeq₂ hκ
    (NumberField.SUnits.exists_ihom_extension_fixed_of_sLevel_of_injective S hpS Sℚ hSℚ F₂' hF₂'
      (Rep.relationModuleInt.ι (Rep.res π₁₂ B)) (Rep.freeCover (Rep.res π₁₂ B)) (relationModuleInt_ι_injective (Rep.res π₁₂ B)) (exact_ι_freeCover (Rep.res π₁₂ B))
      (freeCover_surjective (Rep.res π₁₂ B)) (fun b => hB b) ιE₂ hιE₂)

  obtain ⟨a, rfl⟩ : ∃ a, (H1π _).hom a = x := H1_induction_on x (fun a => ⟨a, rfl⟩)
  have hinfl : Λ₂ ((groupCohomology.map π₁₂ (Rep.extInflR π₁₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) jE₁₂) 1).hom ((H1π _).hom a)) = 0 := by
    erw [H1π_comp_map_apply]
    rw [← hx]
    exact NumberField.SUnits.isGlobalBridge2_apply_inflation_eq S hpS Sℚ hSℚ M F₁ F₂' h₁₂ hF₁ hF₂' π₁₂ hπ₁₂
      (Rep.relationModuleInt.ι B) (Rep.freeCover B) (relationModuleInt_ι_injective B) (exact_ι_freeCover B) (freeCover_surjective B)
      (Rep.relationModuleInt.ι (Rep.res π₁₂ B)) (Rep.freeCover (Rep.res π₁₂ B)) (relationModuleInt_ι_injective (Rep.res π₁₂ B)) (exact_ι_freeCover (Rep.res π₁₂ B))
      (freeCover_surjective (Rep.res π₁₂ B)) hB (Rep.relationModuleInt.resMap π₁₂ B) (Rep.freeResMap π₁₂ B)
      (ι_comp_freeResMap π₁₂ B) (Rep.freeResMap_comp_resFunctor_map_freeCover π₁₂ B).symm
      ιE₁ hιE₁ ιE₂ hιE₂ jE₁₂ hjE₁₂ κ hκeq hκ hΛ₁ hΛ₂ a _ (fun d' x' => rfl)

  obtain ⟨c, hc⟩ : ∃ c, (H2π _).hom c = (groupCohomology.δ (Rep.homSeqOne_shortExact (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)) 1 2 rfl).hom η :=
    H2_induction_on (C := fun y => ∃ c, (H2π _).hom c = y) _ (fun c => ⟨c, rfl⟩)
  let m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M :=
    mRead (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (M := M) (AlgEquiv.restrictNormalHom ↥F₂') (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) ιE₂ κ hκ c
  have hm : ∀ γ₁ γ₂ b, κ b (m (γ₁, γ₂)) = ιE₂ (LinearMap.toAddMonoidHom ((c : _ → _) (AlgEquiv.restrictNormalHom ↥F₂' γ₁, AlgEquiv.restrictNormalHom ↥F₂' γ₂)) b) :=
    κ_mRead (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (M := M) (AlgEquiv.restrictNormalHom ↥F₂') (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) ιE₂ κ hκ c
  have hmS : m ∈ levelCocyclesS₂ S M := by
    rw [mem_levelCocyclesS₂_iff]
    refine ⟨mRead_mem_cocycles₂ (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (M := M) (AlgEquiv.restrictNormalHom ↥F₂') (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) ιE₂ (iotaE_rho F₂' ιE₂ hιE₂) κ hκeq₂ hκ c,
      F₂', hF₂', fun γ₁ γ₂ s s' hs hs' => ?_⟩
    apply κ_inj (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (M := M) (Rep.res π₁₂ B) κ hκ
    intro b
    refine (hm (γ₁ * s) (γ₂ * s') b).trans (Eq.trans ?_ (hm γ₁ γ₂ b).symm)
    rw [map_mul, map_mul, restrictNormalHom_eq_one_of_mem F₂' s hs, restrictNormalHom_eq_one_of_mem F₂' s' hs', mul_one, mul_one]
  have hclass : Λ₂ ((groupCohomology.map (MonoidHom.id _) (Rep.homSeq₂ (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)).f 1).hom η) = continuousH2Sπ S M ⟨m, hmS⟩ :=
    NumberField.SUnits.isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta S hpS Sℚ hSℚ M F₂' hF₂' (Rep.res π₁₂ B)
      (fun b => hB b) (Rep.homSeqOne_shortExact (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ)) ιE₂ hιE₂ (show (Rep.res π₁₂ B) →+ M →+ Additive (AlgebraicClosure ℚ)ˣ from κ)
      hκeq₂ hκ hΛ₂ η c hc m hm hmS
  have hzero : continuousH2Sπ S M ⟨m, hmS⟩ = 0 := by
    refine hclass.symm.trans ?_
    have h := hinfl
    rw [hη] at h
    exact h

  have hcob : m ∈ levelCoboundariesS₂ S M := by
    have := (Submodule.Quotient.mk_eq_zero _).1 hzero
    rw [Submodule.mem_comap] at this
    exact this
  obtain ⟨b, ⟨Fb, hFbS, hb⟩, hbm⟩ := (mem_levelCoboundariesS₂_iff S M m).1 hcob
  refine ⟨Fb, hFbS, ?_⟩

  intro F₃ _ _ h₂₃ hb₃ π₂₃ hπ₂₃ ιE₃ hιE₃ jE₂₃ hjE₂₃
  rw [← hc]
  refine map_H2π_eq_zero (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (M := M) (AlgEquiv.restrictNormalHom ↥F₃) (AlgEquiv.restrictNormalHom_surjective _) π₂₃ (Rep.res π₁₂ B) (NumberField.SUnits.sUnitsRep ℚ ↥F₂' Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ) jE₂₃
    ιE₂ ιE₃ hjE₂₃ (iotaE_injective F₃ ιE₃ hιE₃) (iotaE_rho F₃ ιE₃ hιE₃) κ ?_ ?_ b ?_ c ?_
  ·
    intro γ b₀ mm
    change κ (B.ρ (π₁₂ (π₂₃ (AlgEquiv.restrictNormalHom ↥F₃ γ))) b₀) (M.ρ γ mm) = _
    rw [hπ₂₃, hπ₁₂]
    exact hκeq γ b₀ mm
  ·
    intro b₀ mm
    have h1 : p • κ b₀ mm = 0 := by
      have h := map_nsmul (κ.flip mm) p b₀
      rw [hB b₀, map_zero] at h
      exact h.symm
    have hp : (Additive.toMul (κ b₀ mm)) ^ p = 1 := by
      rw [← toMul_nsmul]
      exact congrArg Additive.toMul h1
    obtain ⟨e₁, he₁⟩ := hμ _ hp
    exact ⟨jE₂₃.hom (jE₁₂.hom e₁), (hjE₂₃ _).trans ((hjE₁₂ _).trans he₁)⟩
  ·
    intro γ s hs
    exact hb γ s (IntermediateField.fixingSubgroup_antitone hb₃ (mem_fixingSubgroup_of_restrictNormalHom_eq_one F₃ s hs))
  ·
    intro γ₁ γ₂ b₀
    rw [hπ₂₃, hπ₂₃]
    erw [hbm]
    exact hm γ₁ γ₂ b₀

end KD2
p2m_reactivate "P2MW.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero.KD2"

namespace KD2

theorem finite_H1_sUnits {Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))} (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁]
    (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] :
    Finite (H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) := by
  haveI := NumberField.SUnits.moduleFinite_sUnitsRep ℚ ↥F₁ Sℚ
  exact Rep.finite_H1_ihom_relationModuleInt B _

theorem isUnramifiedOutside_finset_sup (S : Finset Nat.Primes) {ι : Type} (s : Finset ι)
    (F : ι → IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : ∀ i ∈ s, (F i).IsUnramifiedOutside S) :
    (s.sup F).IsUnramifiedOutside S :=
  Finset.sup_induction (p := fun K : IntermediateField ℚ (AlgebraicClosure ℚ) => K.IsUnramifiedOutside S)
    (IntermediateField.isUnramifiedOutside_bot S) (fun _ h₁ _ h₂ => h₁.sup h₂) hF

theorem numberField_of_finiteDimensional (N : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥N] : NumberField ↥N :=
  { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ ↥N).injective
    to_finiteDimensional := inferInstance }

theorem exists_galois_sLevel_ge (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) :
    ∃ N : IntermediateField ℚ (AlgebraicClosure ℚ), K ≤ N ∧ ∃ (_ : NumberField ↥N) (_ : IsGalois ℚ ↥N), N.IsUnramifiedOutside S := by
  obtain ⟨hle, hfd, hgal, hS⟩ := IntermediateField.isUnramifiedOutside_normalClosure S K hK
  refine ⟨(IntermediateField.normalClosure ℚ ↥K (AlgebraicClosure ℚ)).restrictScalars ℚ, hle, ?_, hgal, hS⟩
  haveI : FiniteDimensional ℚ ↥((IntermediateField.normalClosure ℚ ↥K (AlgebraicClosure ℚ)).restrictScalars ℚ) := hfd
  exact numberField_of_finiteDimensional _

end KD2
p2m_reactivate "P2MW.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero.KD2"

namespace KDC

open NumberField.SUnits

noncomputable def iotaE (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] :
    sUnitsRep ℚ ↥L Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ where
  toFun e := Additive.ofMul (Units.map (algebraMap ↥L (AlgebraicClosure ℚ) : ↥L →* AlgebraicClosure ℚ) (val ℚ ↥L Sℚ e))
  map_zero' := by simp; rfl
  map_add' x y := by rw [val_add, map_mul]; rfl

theorem toMul_iotaE (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
    (e : sUnitsRep ℚ ↥L Sℚ) :
    Additive.toMul (iotaE Sℚ L e) = Units.map (algebraMap ↥L (AlgebraicClosure ℚ) : ↥L →* AlgebraicClosure ℚ) (val ℚ ↥L Sℚ e) := rfl

section step

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
  (F₁ F₂' F₃ : IntermediateField ℚ (AlgebraicClosure ℚ))
  [NumberField ↥F₁] [IsGalois ℚ ↥F₁] [NumberField ↥F₂'] [IsGalois ℚ ↥F₂'] [NumberField ↥F₃] [IsGalois ℚ ↥F₃]
  (h₁₂ : F₁ ≤ F₂') (h₂₃ : F₂' ≤ F₃)
  (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] (hB : ∀ b : B, p • b = 0)
  (hdiv : ∀ e : sUnitsRep ℚ ↥F₁ Sℚ, ∃ e' : sUnitsRep ℚ ↥F₂' Sℚ, (sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ).hom e = p • e')

set_option maxHeartbeats 3200000 in

theorem step
    (ιE₁ : sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₁ : ∀ x, Additive.toMul (ιE₁ x) = Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (val ℚ ↥F₁ Sℚ x))
    (π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
    (hπ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
    (ιE₃ : sUnitsRep ℚ ↥F₃ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₃ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (val ℚ ↥F₃ Sℚ x))
    (jE : Rep.res π (sUnitsRep ℚ ↥F₁ Sℚ) ⟶ sUnitsRep ℚ ↥F₃ Sℚ) (hjE : ∀ x, ιE₃ (jE.hom x) = ιE₁ x)
    (x : H1 ((ihom (Rep.relationModuleInt B)).obj (sUnitsRep ℚ ↥F₁ Sℚ)))
    (key : (groupCohomology.map (levelHom F₂' F₃ h₂₃)
        (KD.homB (levelHom F₂' F₃ h₂₃) (Rep.res (levelHom F₁ F₂' h₁₂) B) (sUnitsRep ℚ ↥F₂' Sℚ) (sUnitsRep ℚ ↥F₃ Sℚ)
          (sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ)) 2).hom
        ((groupCohomology.δ (Rep.homSeqOne_shortExact (Rep.res (levelHom F₁ F₂' h₁₂) B) (sUnitsRep ℚ ↥F₂' Sℚ)) 1 2 rfl).hom
          (KD.eta (levelHom F₁ F₂' h₁₂) B (sUnitsRep ℚ ↥F₁ Sℚ) (sUnitsRep ℚ ↥F₂' Sℚ) (sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) hB hdiv x)) = 0) :
    (groupCohomology.map π (Rep.extInflR π B (sUnitsRep ℚ ↥F₁ Sℚ) (sUnitsRep ℚ ↥F₃ Sℚ) jE) 1).hom x = 0 := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hAC : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

  have hπfac : π = (levelHom F₁ F₂' h₁₂).comp (levelHom F₂' F₃ h₂₃) := by
    refine MonoidHom.ext fun τ => ?_
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) τ
    rw [hπ, MonoidHom.comp_apply, levelHom_restrictNormalHom, levelHom_restrictNormalHom]
  subst hπfac

  have hjEfac : jE = (Rep.resFunctor (levelHom F₂' F₃ h₂₃)).map (sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) ≫ sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ := by
    apply Rep.hom_ext
    refine DFunLike.ext _ _ fun e => ιE_injective Sℚ F₃ ιE₃ hιE₃ (Additive.toMul.injective ?_)
    rw [hjE, hιE₁, hιE₃]
    exact ((map_val_sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ _).trans (map_val_sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ e)).symm
  subst hjEfac

  rw [KD.inf_comp, KD.inf_eq_psi_eta (levelHom F₁ F₂' h₁₂) B (sUnitsRep ℚ ↥F₁ Sℚ) (sUnitsRep ℚ ↥F₂' Sℚ)
    (sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) hB hdiv x]
  refine (KD.inf_psi_eq_psi_homQ (levelHom F₂' F₃ h₂₃) (Rep.res (levelHom F₁ F₂' h₁₂) B) _ _
    (sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ) _).trans ?_

  haveI : Fintype (↥F₃ ≃ₐ[ℚ] ↥F₃) := Fintype.ofFinite _
  have hz : (groupCohomology.map (levelHom F₂' F₃ h₂₃)
      (KD.homQ (levelHom F₂' F₃ h₂₃) (Rep.res (levelHom F₁ F₂' h₁₂) B) (sUnitsRep ℚ ↥F₂' Sℚ) (sUnitsRep ℚ ↥F₃ Sℚ)
        (sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ)) 1).hom
      (KD.eta (levelHom F₁ F₂' h₁₂) B (sUnitsRep ℚ ↥F₁ Sℚ) (sUnitsRep ℚ ↥F₂' Sℚ) (sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) hB hdiv x) = 0 := by
    apply KD.eq_zero_of_delta_eq_zero
    rw [KD.delta_homQ_eq_homB_delta]
    exact key
  rw [hz, map_zero]
  rfl

end step
p2m_reactivate "P2MW.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero.KD2"

end KDC
p2m_reactivate "P2MW.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero.KD2"

set_option maxHeartbeats 1600000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S)
    (hFM : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m)
    (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] (hB : ∀ b : B, p • b = 0)

    (ιE₁ : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₁ : ∀ x, Additive.toMul (ιE₁ x) = Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ x))
    (hμ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ, ιE₁ e = Additive.ofMul u)

    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)

    {Λ₁ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →+ continuousH2S S M}
    (hΛ₁ : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F₁) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE₁ κ Λ₁) :
    ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₂ ∧ FiniteDimensional ℚ ↥F₂ ∧ IsGalois ℚ ↥F₂ ∧ F₂.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] [IsGalois ℚ ↥F₃] (_ : F₂ ≤ F₃)
        (π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
        (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
        (ιE₃ : NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
        (_ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ x))
        (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ)
        (_ : ∀ x, ιE₃ (jE.hom x) = ιE₁ x)
        (x : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) (_ : Λ₁ x = 0),
        (groupCohomology.map π (Rep.extInflR π B (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ) jE) 1).hom x = 0 := by
  classical

  obtain ⟨F₂', h₁₂, hfd₂, hgal₂, hS₂, hK⟩ :=
    NumberField.SUnits.exists_sLevel_forall_sUnitsRep_map_val_eq_pow S hpS Sℚ hSℚ F₁ hF₁
  haveI := hfd₂
  haveI := hgal₂
  haveI : NumberField ↥F₂' := KD2.numberField_of_finiteDimensional F₂'
  have hjE₁₂ : ∀ e, KDC.iotaE Sℚ F₂' ((KDC.sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ).hom e) = ιE₁ e := fun e =>
    Additive.toMul.injective (by rw [KDC.toMul_iotaE, hιE₁]; exact KDC.map_val_sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ e)
  have hdiv : ∀ e, ∃ e', (KDC.sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ).hom e = p • e' :=
    KDC.forall_exists_eq_nsmul Sℚ F₁ F₂' ιE₁ hιE₁ (KDC.iotaE Sℚ F₂') (KDC.toMul_iotaE Sℚ F₂')
      (KDC.sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) hjE₁₂ (fun e => hK F₂' le_rfl e)

  have SA := fun (x : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) (hx : Λ₁ x = 0) =>
    KD2.primitive_vanishes S hpS Sℚ hSℚ M F₁ hF₁ hFM B hB ιE₁ hιE₁ hμ κ hκeq hκ hΛ₁ F₂' h₁₂ hS₂
      (KDC.levelHom F₁ F₂' h₁₂) (KDC.levelHom_restrictNormalHom F₁ F₂' h₁₂) (KDC.iotaE Sℚ F₂') (KDC.toMul_iotaE Sℚ F₂')
      (KDC.sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) hjE₁₂ hdiv x hx
      (KD.eta (KDC.levelHom F₁ F₂' h₁₂) B _ _ (KDC.sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) hB hdiv x)
      (KD.inf_eq_psi_eta (KDC.levelHom F₁ F₂' h₁₂) B _ _ (KDC.sUnitsIncl F₁ F₂' h₁₂ S Sℚ hSℚ) hB hdiv x)
  haveI : Fintype (H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) :=
    @Fintype.ofFinite _ (KD2.finite_H1_sUnits F₁ B)
  let Fb : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →
      IntermediateField ℚ (AlgebraicClosure ℚ) := fun x => if hx : Λ₁ x = 0 then (SA x hx).choose else ⊥
  have hFb : ∀ x, (Fb x).IsUnramifiedOutside S := fun x => by
    by_cases hx : Λ₁ x = 0
    · have e : Fb x = (SA x hx).choose := dif_pos hx
      rw [e]
      exact (SA x hx).choose_spec.1
    · have e : Fb x = ⊥ := dif_neg hx
      rw [e]
      exact IntermediateField.isUnramifiedOutside_bot S

  have hKS : (F₂' ⊔ Finset.univ.sup Fb).IsUnramifiedOutside S :=
    hS₂.sup (KD2.isUnramifiedOutside_finset_sup S _ Fb fun x _ => hFb x)
  obtain ⟨N, hKN, instN, instG, hNS⟩ := KD2.exists_galois_sLevel_ge S _ hKS
  haveI := instN
  haveI := instG
  refine ⟨N, h₁₂.trans (le_sup_left.trans hKN), inferInstance, instG, hNS, ?_⟩
  intro F₃ _ _ hN₃ π hπ ιE₃ hιE₃ jE hjE x hx
  have h₂₃ : F₂' ≤ F₃ := le_sup_left.trans (hKN.trans hN₃)
  have hb₃ : (SA x hx).choose ≤ F₃ := by
    have e : Fb x = (SA x hx).choose := dif_pos hx
    rw [← e]
    exact (Finset.le_sup (Finset.mem_univ x)).trans (le_sup_right.trans (hKN.trans hN₃))
  have hjE₂₃ : ∀ e, ιE₃ ((KDC.sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ).hom e) = KDC.iotaE Sℚ F₂' e := fun e =>
    Additive.toMul.injective (by rw [hιE₃, KDC.toMul_iotaE]; exact KDC.map_val_sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ e)
  have key := (SA x hx).choose_spec.2 F₃ h₂₃ hb₃ (KDC.levelHom F₂' F₃ h₂₃) (KDC.levelHom_restrictNormalHom F₂' F₃ h₂₃)
    ιE₃ hιE₃ (KDC.sUnitsIncl F₂' F₃ h₂₃ S Sℚ hSℚ) hjE₂₃
  exact KDC.step S Sℚ hSℚ F₁ F₂' F₃ h₁₂ h₂₃ B hB hdiv ιE₁ hιE₁ π hπ ιE₃ hιE₃ jE hjE x key

end S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
end P2MW
export P2MW.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero (solution)
