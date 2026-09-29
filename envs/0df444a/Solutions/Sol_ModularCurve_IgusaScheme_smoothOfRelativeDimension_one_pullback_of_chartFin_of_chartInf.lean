-- Prove2me | solution 1 for ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ff094d74-960d-534b-bce9-eb273d2d3682

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme

noncomputable section

set_option autoImplicit false

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type) [Field k] (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k)
    (hFin : SmoothOfRelativeDimension 1
      (pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ))))
        (Spec.map (CommRingCat.ofHom φ))))
    (hInf : SmoothOfRelativeDimension 1
      (pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ))))
        (Spec.map (CommRingCat.ofHom φ)))) :
    SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) := by
  classical
  set g := Spec.map (CommRingCat.ofHom φ) with hg

  let gFin : pullback (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)))) g ⟶
      pullback (igusaTo N ℓ) g :=
    pullback.map _ _ _ _ (ιFin N ℓ) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ιFin_igusaTo]) (by rw [Category.comp_id, Category.id_comp])
  let gInf : pullback (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)))) g ⟶
      pullback (igusaTo N ℓ) g :=
    pullback.map _ _ _ _ (ιInf N ℓ) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ιInf_igusaTo]) (by rw [Category.comp_id, Category.id_comp])
  haveI hgFinOI : IsOpenImmersion gFin := inferInstance
  haveI hgInfOI : IsOpenImmersion gInf := inferInstance
  have hgFinSnd : gFin ≫ pullback.snd (igusaTo N ℓ) g =
      pullback.snd _ _ := by first
      | simp only [gFin, pullback.map_snd, Category.comp_id]
      | simp only [gFin, pullback.lift_snd, Category.comp_id]
      | simp [gFin]
  have hgInfSnd : gInf ≫ pullback.snd (igusaTo N ℓ) g =
      pullback.snd _ _ := by first
      | simp only [gInf, pullback.map_snd, Category.comp_id]
      | simp only [gInf, pullback.lift_snd, Category.comp_id]
      | simp [gInf]
  have hF2 : SmoothOfRelativeDimension 1 (gFin ≫ pullback.snd (igusaTo N ℓ) g) := hgFinSnd ▸ hFin
  have hI2 : SmoothOfRelativeDimension 1 (gInf ≫ pullback.snd (igusaTo N ℓ) g) := hgInfSnd ▸ hInf
  have hgFinFst : gFin ≫ pullback.fst (igusaTo N ℓ) g =
      pullback.fst _ _ ≫ ιFin N ℓ := by first
      | simp only [gFin, pullback.map_fst, Category.comp_id]
      | simp only [gFin, pullback.lift_fst, Category.comp_id]
      | simp [gFin]
  have hgInfFst : gInf ≫ pullback.fst (igusaTo N ℓ) g =
      pullback.fst _ _ ≫ ιInf N ℓ := by first
      | simp only [gInf, pullback.map_fst, Category.comp_id]
      | simp only [gInf, pullback.lift_fst, Category.comp_id]
      | simp [gInf]

  have hpc : pullback.snd (igusaTo N ℓ) g ≫ g = pullback.fst (igusaTo N ℓ) g ≫ igusaTo N ℓ :=
    (pullback.condition (f := igusaTo N ℓ) (g := g)).symm
  have hBot : IsPullback (pullback.snd (igusaTo N ℓ) g) (pullback.fst (igusaTo N ℓ) g)
      g (igusaTo N ℓ) := (IsPullback.of_hasPullback (igusaTo N ℓ) g).flip
  have hOutFin : IsPullback (gFin ≫ pullback.snd (igusaTo N ℓ) g)
      (pullback.fst _ g) g (ιFin N ℓ ≫ igusaTo N ℓ) :=
    hgFinSnd.symm ▸ (ιFin_igusaTo N ℓ).symm ▸
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)))) g).flip
  have hOutInf : IsPullback (gInf ≫ pullback.snd (igusaTo N ℓ) g)
      (pullback.fst _ g) g (ιInf N ℓ ≫ igusaTo N ℓ) :=
    hgInfSnd.symm ▸ (ιInf_igusaTo N ℓ).symm ▸
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)))) g).flip
  have hpbFin : IsPullback gFin (pullback.fst _ g)
      (pullback.fst (igusaTo N ℓ) g) (ιFin N ℓ) := by
    exact hOutFin.of_right hgFinFst hBot
  have hpbInf : IsPullback gInf (pullback.fst _ g)
      (pullback.fst (igusaTo N ℓ) g) (ιInf N ℓ) := by
    exact hOutInf.of_right hgInfFst hBot

  haveI hιFinOI : IsOpenImmersion (ιFin N ℓ) := inferInstance
  haveI hιInfOI : IsOpenImmersion (ιInf N ℓ) := inferInstance
  have hrFin : Set.range gFin.base =
      (pullback.fst (igusaTo N ℓ) g).base ⁻¹' Set.range (ιFin N ℓ).base := by
    have hsurj : Function.Surjective hpbFin.isoPullback.hom.base :=
      (ConcreteCategory.bijective_of_isIso hpbFin.isoPullback.hom.base).2
    have hstep : Set.range gFin.base =
        Set.range (pullback.fst (pullback.fst (igusaTo N ℓ) g) (ιFin N ℓ)).base := by
      apply le_antisymm
      · rintro _ ⟨w, rfl⟩
        refine ⟨hpbFin.isoPullback.hom.base w, ?_⟩
        conv_rhs => rw [← hpbFin.isoPullback_hom_fst]
        first
        | rfl
        | exact (Scheme.comp_base_apply _ _ _).symm
        | simp
      · rintro _ ⟨y, rfl⟩
        obtain ⟨w, rfl⟩ := hsurj y
        refine ⟨w, ?_⟩
        conv_lhs => rw [← hpbFin.isoPullback_hom_fst]
        first
        | rfl
        | exact Scheme.comp_base_apply _ _ _
        | simp
    rw [hstep, IsOpenImmersion.range_pullbackFst]
    first
    | done
    | rfl
    | simp only [Scheme.Hom.coe_opensRange]
    | simp
  have hrInf : Set.range gInf.base =
      (pullback.fst (igusaTo N ℓ) g).base ⁻¹' Set.range (ιInf N ℓ).base := by
    have hsurj : Function.Surjective hpbInf.isoPullback.hom.base :=
      (ConcreteCategory.bijective_of_isIso hpbInf.isoPullback.hom.base).2
    have hstep : Set.range gInf.base =
        Set.range (pullback.fst (pullback.fst (igusaTo N ℓ) g) (ιInf N ℓ)).base := by
      apply le_antisymm
      · rintro _ ⟨w, rfl⟩
        refine ⟨hpbInf.isoPullback.hom.base w, ?_⟩
        conv_rhs => rw [← hpbInf.isoPullback_hom_fst]
        first
        | rfl
        | exact (Scheme.comp_base_apply _ _ _).symm
        | simp
      · rintro _ ⟨y, rfl⟩
        obtain ⟨w, rfl⟩ := hsurj y
        refine ⟨w, ?_⟩
        conv_lhs => rw [← hpbInf.isoPullback_hom_fst]
        first
        | rfl
        | exact Scheme.comp_base_apply _ _ _
        | simp
    rw [hstep, IsOpenImmersion.range_pullbackFst]
    first
    | done
    | rfl
    | simp only [Scheme.Hom.coe_opensRange]
    | simp

  have hcov : ∀ x : ↥(pullback (igusaTo N ℓ) g),
      x ∈ Set.range gFin.base ∨ x ∈ Set.range gInf.base := by
    intro x
    rcases mem_range_ιFin_or_mem_range_ιInf N ℓ ((pullback.fst (igusaTo N ℓ) g).base x)
      with hF | hI
    · exact Or.inl (hrFin ▸ hF)
    · exact Or.inr (hrInf ▸ hI)

  let 𝒰 : (pullback (igusaTo N ℓ) g).OpenCover :=
    Scheme.Cover.mkOfCovers (ULift.{0} Bool)
      (fun b => if b.down then
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)))) g
        else pullback (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)))) g)
      (fun b => match b with
        | ⟨true⟩ => gFin
        | ⟨false⟩ => gInf)
      (fun x => by
        rcases hcov x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact ⟨⟨true⟩, y, hy⟩
        · exact ⟨⟨false⟩, y, hy⟩)
      (map_prop := fun b => match b with
        | ⟨true⟩ => hgFinOI
        | ⟨false⟩ => hgInfOI)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1) 𝒰 ?_
  rintro ⟨(_ | _)⟩
  · exact hI2
  · exact hF2

end
end S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf (solution)
