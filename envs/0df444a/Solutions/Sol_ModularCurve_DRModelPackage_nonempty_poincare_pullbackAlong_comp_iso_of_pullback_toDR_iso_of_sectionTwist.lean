-- Prove2me | solution 1 for ModularCurve.DRModelPackage.nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1802955b-bad1-56c0-ba7a-83fe790a8422

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization
open Opposite

universe u

noncomputable section

namespace K6aKit

theorem isIso_pullback_snd_of_isIso_morphismRestrict {X Y T : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens)
    [hU : IsIso (g ∣_ U)] (h : T ⟶ X) (hh : Set.range h.base ⊆ (U : Set X)) : IsIso (pullback.snd g h) := by
  let h' : T ⟶ U := IsOpenImmersion.lift U.ι h (by rwa [Scheme.Opens.range_ι])
  have hh' : h' ≫ U.ι = h := IsOpenImmersion.lift_fac _ _ _
  have sq := (IsPullback.of_hasPullback (g ∣_ U) h').paste_horiz (isPullback_morphismRestrict g U).flip
  rw [← hh', ← sq.isoPullback_inv_snd]
  infer_instance

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

theorem smooth_drModel_baseChange (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    {K : Type} [CommRing K] (tK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℤ))
    (s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of K))
    (hs : s ≫ tK = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) s) :
    SmoothOfRelativeDimension 1 (pullback.snd (DRModel.toBase p) tK) := by
  haveI := 𝔛.eη_iso
  let c := DRModel.toBase p
  let tQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))
  have hs' : s ≫ tK = tQ := hs
  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd c tQ) :=
    smoothOfRelativeDimension_one_of_iso (f := 𝔛.Mη.toBase) (asIso 𝔛.eη) (by rw [← 𝔛.heη, asIso_inv, IsIso.inv_hom_id_assoc])
  let e : pullback s (pullback.snd c tK) ≅ pullback c tQ :=
    pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso c tK s ≪≫ pullback.congrHom rfl hs'
  haveI : SmoothOfRelativeDimension 1 (pullback.fst s (pullback.snd c tK)) := by
    refine smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tQ) e.symm ?_
    simp only [Iso.symm_inv, e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]
  exact (SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact 1).of_isPullback
    (IsPullback.of_hasPullback s (pullback.snd c tK)) hQ ‹_›

theorem ofPoint_I_congr {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (ha : a ≫ f = g) (ha' : a' ≫ f = g) (h : a = a') :
    (RelEffCartierDiv.ofPoint f a ha).I = (RelEffCartierDiv.ofPoint f a' ha').I := by
  subst h; rfl

def invUnique {X : Scheme.{u}} {L M M' : X.Modules} (e : L ⊗ M ≅ 𝟙_ X.Modules) (e' : L ⊗ M' ≅ 𝟙_ X.Modules) : M ≅ M' :=
  (λ_ M).symm ≪≫ whiskerRightIso (β_ M' L ≪≫ e').symm M ≪≫ α_ M' L M ≪≫ whiskerLeftIso M' e ≪≫ ρ_ M'

theorem nonempty_pullback_module_iso {X X' : Scheme.{u}} (f : X' ⟶ X) {I : X.IdealSheafData} {J : X'.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (e : (Scheme.Modules.pullback f).obj I.invModule ≅ J.invModule) :
    Nonempty ((Scheme.Modules.pullback f).obj I.module ≅ J.module) := by

  obtain ⟨eI⟩ := (Scheme.Modules.IsInvertible.dual (Scheme.IdealSheafData.IsInvertible.isInvertible_module hI)).2
  obtain ⟨eJ⟩ := (Scheme.Modules.IsInvertible.dual (Scheme.IdealSheafData.IsInvertible.isInvertible_module hJ)).2
  have e1 : J.invModule ⊗ (Scheme.Modules.pullback f).obj I.module ≅ 𝟙_ _ :=
    whiskerRightIso e.symm _ ≪≫ (β_ _ _) ≪≫ (Scheme.Modules.pullbackTensorObjIso f _ _).symm ≪≫
      (Scheme.Modules.pullback f).mapIso eI ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f
  have e2 : J.invModule ⊗ J.module ≅ 𝟙_ _ := β_ _ _ ≪≫ eJ
  exact ⟨invUnique e1 e2⟩

theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp only [pow_zero]; try exact Scheme.IdealSheafData.comap_top f
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

end K6aKit

end

set_option maxHeartbeats 3200000 in

theorem solution
    (p : ℕ) [Fact p.Prime]
    (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    [IsProper (DRModel.toBase p)]
    (O : Type) [CommRing O] [IsDomain O]
    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) D.toBase)
    (M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules)
    (eMz : Nonempty ((hD.poincare.pullbackAlong z).L ≅ M))
    (Y : Scheme.{0}) (toBase : Y ⟶ Spec (CommRingCat.of O))
    (toDR : Y ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    (toDR_over : toDR ≫ pullback.snd _ _ = toBase) [IsProper toBase]
    (toDR_iso_generic : IsIso (toDR ∣_ (pullback.snd (DRModel.toBase p) _ ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))))
    (L : Y.Modules) (eM : Nonempty ((Scheme.Modules.pullback toDR).obj M ≅ L))
    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) toBase) (pos neg : Fin m → ℕ)
    (hLgen : Nonempty ((Scheme.Modules.pullback (pullback.fst toBase
          (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O)))))).obj L ≅
        (List.finRange m).foldr
          (fun j N => (sectionTwist toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _)))) (pos j) ⊗
              ((sectionIdeal toBase (σ j) (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))) ^ (neg j)).module) ⊗ N)
          (𝟙_ (pullback toBase (Spec.map (CommRingCat.ofHom (algebraMap _ (FractionRing _))))).Modules)))
    (τ : O →+* AlgebraicClosure ℚ) (τF : FractionRing O →+* AlgebraicClosure ℚ)
    (hτ : τF.comp (algebraMap O (FractionRing O)) = τ)
    (q : Fin m → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Mη.C // q ≫ 𝔛.Mη.toBase = 𝟙 _})
    (hqσ : ∀ j, (q j).1 ≫ 𝔛.eη ≫
        pullback.map (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
          (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) (𝟙 _) (Spec.map (CommRingCat.ofHom τ)) (𝟙 _)
          (by simp)
          (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _) =
      Spec.map (CommRingCat.ofHom τ) ≫ (σ j).1 ≫ toDR) :
    Nonempty ((hD.poincare.pullbackAlong ⟨Spec.map (CommRingCat.ofHom τ) ≫ z.1, by
        rw [Category.assoc, z.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext_int _ _⟩).L ≅
      (List.finRange m).foldr (fun j M =>
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _)
              (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2])).I ^ (neg j)).module ⊗ M)
        (𝟙_ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).Modules)) := by
  haveI := 𝔛.eη_iso
  subst toDR_over
  obtain ⟨eMz⟩ := eMz
  obtain ⟨eM⟩ := eM
  obtain ⟨hL⟩ := hLgen

  let Qb := AlgebraicClosure ℚ
  let F := FractionRing O
  let c := DRModel.toBase p
  let tO : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let c' := toDR ≫ pullback.snd c tO
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Qb))
  let tZF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ F))
  let tb : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom τ)
  let tF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O F))
  let sF : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom τF)
  have htb : tb ≫ tO = tQ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; all_goals (congr 2; exact RingHom.ext_int _ _)
  have htF : tF ≫ tO = tZF := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; all_goals (congr 2; exact RingHom.ext_int _ _)
  have hsF : sF ≫ tF = tb := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]

  have hτp : τ (p : O) ≠ 0 := by
    rw [map_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpO : ((p : ℕ) : O) ≠ 0 := fun h => hτp (by rw [h, map_zero])
  have hpF : algebraMap O F (p : O) ≠ 0 := fun h =>
    hpO ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective O F) _ h)
  let U : (Spec (CommRingCat.of O)).Opens := PrimeSpectrum.basicOpen ((p : ℕ) : O)
  have hmemU : ∀ {K : Type} [Field K] (f : O →+* K), f (p : O) ≠ 0 →
      Set.range (Spec.map (CommRingCat.ofHom f)).base ⊆ (U : Set _) := by
    intro K _ f hf
    rintro _ ⟨x, rfl⟩
    have hx : x.asIdeal = ⊥ := (Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top
    show ((p : ℕ) : O) ∉ ((Spec.map (CommRingCat.ofHom f)).base x).asIdeal
    rw [Spec.map_base]
    show ((p : ℕ) : O) ∉ Ideal.comap f x.asIdeal
    rw [hx, Ideal.mem_comap, Ideal.mem_bot]
    exact hf

  have mkIso : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of O)) (ht : Set.range t.base ⊆ (U : Set _))
      (t' : T ⟶ Spec (CommRingCat.of ℤ)) (htt : t ≫ tO = t'),
      ∃ eY : pullback c' t ≅ pullback c t',
        eY.hom ≫ pullback.snd c t' = pullback.snd c' t ∧
        eY.hom ≫ pullback.fst c t' = pullback.fst c' t ≫ toDR ≫ pullback.fst c tO := by
    intro T t ht t' htt
    subst htt
    let h := pullback.fst (pullback.snd c tO) t
    have hh : Set.range h.base ⊆ ((pullback.snd c tO ⁻¹ᵁ U : (pullback c tO).Opens) : Set _) := by
      rintro _ ⟨x, rfl⟩
      show (pullback.snd c tO).base (h.base x) ∈ (U : Set _)
      show (h ≫ pullback.snd c tO).base x ∈ (U : Set _)
      rw [pullback.condition]
      exact ht ⟨_, rfl⟩
    haveI : IsIso (pullback.snd toDR h) := K6aKit.isIso_pullback_snd_of_isIso_morphismRestrict toDR _ h hh
    let e2 : pullback c' t ≅ pullback toDR h := (pullbackRightPullbackFstIso (pullback.snd c tO) t toDR).symm
    let e4 : pullback toDR h ≅ pullback (pullback.snd c tO) t := asIso (pullback.snd toDR h)
    let e5 : pullback (pullback.snd c tO) t ≅ pullback c (t ≫ tO) := pullbackLeftPullbackSndIso c tO t
    refine ⟨e2 ≪≫ e4 ≪≫ e5, ?_, ?_⟩
    · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, asIso_hom,
        Iso.symm_hom, pullbackRightPullbackFstIso_inv_snd_snd]
    · rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, asIso_hom,
        ← pullback.condition_assoc, Iso.symm_hom, pullbackRightPullbackFstIso_inv_fst_assoc]
  obtain ⟨eY, heY1, heY2⟩ := mkIso tb (hmemU τ hτp) tQ htb
  obtain ⟨eYF, heYF1, heYF2⟩ := mkIso tF (hmemU (algebraMap O F) hpF) tZF htF

  haveI hsmX : SmoothOfRelativeDimension 1 (pullback.snd c tQ) :=
    K6aKit.smoothOfRelativeDimension_one_of_iso (f := 𝔛.Mη.toBase) (asIso 𝔛.eη)
      (by rw [← 𝔛.heη, asIso_inv, IsIso.inv_hom_id_assoc])
  haveI hsmF : SmoothOfRelativeDimension 1 (pullback.snd c tZF) := by
    refine K6aKit.smooth_drModel_baseChange p 𝔛 tZF sF ?_ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; all_goals (congr 2; exact RingHom.ext_int _ _)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c' tb) :=
    K6aKit.smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tQ) eY.symm heY1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c' tF) :=
    K6aKit.smoothOfRelativeDimension_one_of_iso (f := pullback.snd c tZF) eYF.symm heYF1

  have hIF : ∀ j, (sectionIdeal c' (σ j) tF).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' tF) _ (pullback.lift_snd _ _ _)
  have hIb : ∀ j, (sectionIdeal c' (σ j) tb).IsInvertible := fun j =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' tb) _ (pullback.lift_snd _ _ _)
  have hx : ∀ j, ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) ≫ DRModel.toBase p = tQ := fun j => by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% 𝔛.heη, reassoc_of% (q j).2]
  have hIX : ∀ j, (RelEffCartierDiv.ofPoint c ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I.IsInvertible :=
    fun j => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tQ) _ (graphOver_snd _ _ _)

  let ψb : SchemeHomOver tQ tO := ⟨tb, htb⟩
  let bO := baseChangeSnd c ψb
  let zb : SchemeHomOver tQ D.toBase := ⟨tb ≫ z.1, by rw [Category.assoc, z.2, htb]⟩
  have hzb : postComp z ψb = zb := Subtype.ext rfl
  have PA : (hD.poincare.pullbackAlong zb).L ≅ (Scheme.Modules.pullback bO).obj M :=
    (Scheme.Modules.pullbackCongr (show baseChangeSnd c zb = bO ≫ baseChangeSnd c z by
        rw [← hzb, baseChangeSnd_comp])).app _ ≪≫
      ((Scheme.Modules.pullbackComp bO (baseChangeSnd c z)).app _).symm ≪≫
      (Scheme.Modules.pullback bO).mapIso eMz

  have heYbO : eY.hom ≫ bO = pullback.fst c' tb ≫ toDR := by
    apply pullback.hom_ext
    · rw [Category.assoc, BaseChange.baseChangeSnd_fst', heY2, Category.assoc]
    · rw [Category.assoc, BaseChange.baseChangeSnd_snd', reassoc_of% heY1, Category.assoc, pullback.condition]
  let ψF : SchemeHomOver tb tF := ⟨sF, hsF⟩
  let bF := baseChangeSnd c' ψF
  have PB : (Scheme.Modules.pullback eY.hom).obj ((Scheme.Modules.pullback bO).obj M) ≅
      (Scheme.Modules.pullback bF).obj ((List.finRange m).foldr
          (fun j N => (sectionTwist c' (σ j) tF (pos j) ⊗ ((sectionIdeal c' (σ j) tF) ^ (neg j)).module) ⊗ N) (𝟙_ _)) :=
    (Scheme.Modules.pullbackComp eY.hom bO).app M ≪≫
      (Scheme.Modules.pullbackCongr heYbO).app M ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst c' tb) toDR).app M).symm ≪≫
      (Scheme.Modules.pullback (pullback.fst c' tb)).mapIso eM ≪≫
      (Scheme.Modules.pullbackCongr (BaseChange.baseChangeSnd_fst' O c' ψF).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp bF (pullback.fst c' tF)).app L).symm ≪≫
      (Scheme.Modules.pullback bF).mapIso hL

  have hcomap : ∀ j (n : ℕ), ((sectionIdeal c' (σ j) tF) ^ n).comap bF = (sectionIdeal c' (σ j) tb) ^ n := by
    intro j n
    rw [K6aKit.comap_pow]
    congr 1
    have h1 := congrArg RelEffCartierDiv.I
      (RelEffCartierDiv.pullbackAlong_ofPoint c' (tF ≫ (σ j).1)
        (by rw [Category.assoc, (σ j).2, Category.comp_id]) sF hsF)
    have h2 : (RelEffCartierDiv.ofPoint c' (sF ≫ tF ≫ (σ j).1) (by rw [Category.assoc, Category.assoc, (σ j).2, Category.comp_id, hsF])).I =
        (RelEffCartierDiv.ofPoint c' (tb ≫ (σ j).1) (by rw [Category.assoc, (σ j).2, Category.comp_id])).I :=
      K6aKit.ofPoint_I_congr _ _ (by rw [← Category.assoc, hsF])
    exact h1.trans h2
  have jA : ∀ j (n : ℕ), Nonempty ((Scheme.Modules.pullback bF).obj (((sectionIdeal c' (σ j) tF) ^ n).invModule) ≅
      ((sectionIdeal c' (σ j) tb) ^ n).invModule) := by
    intro j n
    have hI' : ((((sectionIdeal c' (σ j) tF) ^ n).comap bF)).IsInvertible := by rw [hcomap]; exact (hIb j).pow n
    obtain ⟨e⟩ := ((hIF j).pow n).nonempty_pullback_invModule_iso bF hI'
    exact ⟨e ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (hcomap j n))⟩
  have jB : ∀ j (n : ℕ), Nonempty ((Scheme.Modules.pullback bF).obj (((sectionIdeal c' (σ j) tF) ^ n).module) ≅
      ((sectionIdeal c' (σ j) tb) ^ n).module) := fun j n =>
    K6aKit.nonempty_pullback_module_iso bF ((hIF j).pow n) ((hIb j).pow n) (jA j n).some
  have PC : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback bF).obj (l.foldr
        (fun j N => (sectionTwist c' (σ j) tF (pos j) ⊗ ((sectionIdeal c' (σ j) tF) ^ (neg j)).module) ⊗ N) (𝟙_ _)) ≅
      l.foldr (fun j N => (sectionTwist c' (σ j) tb (pos j) ⊗ ((sectionIdeal c' (σ j) tb) ^ (neg j)).module) ⊗ N) (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact ⟨Scheme.Modules.pullbackTensorUnitObjIso bF⟩
    | cons j l ih =>
      exact ⟨Scheme.Modules.pullbackTensorObjIso bF _ _ ≪≫
        ((Scheme.Modules.pullbackTensorObjIso bF _ _ ≪≫ ((jA j (pos j)).some ⊗ᵢ (jB j (neg j)).some)) ⊗ᵢ ih.some)⟩

  have hσb : ∀ j, (tb ≫ (σ j).1) ≫ c' = tb := fun j => by rw [Category.assoc, (σ j).2, Category.comp_id]
  have hgraph : ∀ j, graphOver c ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) (hx j) ≫ eY.inv =
      graphOver c' (tb ≫ (σ j).1) (hσb j) := by
    intro j
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, heY2, graphOver_fst, graphOver_fst_assoc]
      have h0 : (q j).1 ≫ 𝔛.eη ≫ bO = tb ≫ (σ j).1 ≫ toDR := hqσ j
      have h1 := congrArg (· ≫ pullback.fst c tO) h0
      simp only [Category.assoc, show bO = baseChangeSnd c ψb from rfl, BaseChange.baseChangeSnd_fst'] at h1
      exact h1
    · rw [Category.assoc, heY1, graphOver_snd, graphOver_snd]
  have jX : ∀ j (n : ℕ),
      Nonempty ((Scheme.Modules.pullback eY.inv).obj (((sectionIdeal c' (σ j) tb) ^ n).invModule) ≅
        ((RelEffCartierDiv.ofPoint c ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback eY.inv).obj (((sectionIdeal c' (σ j) tb) ^ n).module) ≅
        ((RelEffCartierDiv.ofPoint c ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ n).module) :=
    fun j n => Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso eY.inv _ _ (hgraph j) (hIb j) (hIX j) n
  have PD : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback eY.inv).obj (l.foldr
        (fun j N => (sectionTwist c' (σ j) tb (pos j) ⊗ ((sectionIdeal c' (σ j) tb) ^ (neg j)).module) ⊗ N) (𝟙_ _)) ≅
      l.foldr (fun j M =>
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ (pos j)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (DRModel.toBase p) ((q j).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _) (hx j)).I ^ (neg j)).module ⊗ M)
        (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact ⟨Scheme.Modules.pullbackTensorUnitObjIso eY.inv⟩
    | cons j l ih =>
      exact ⟨Scheme.Modules.pullbackTensorObjIso eY.inv _ _ ≪≫
        ((Scheme.Modules.pullbackTensorObjIso eY.inv _ _ ≪≫ ((jX j (pos j)).1.some ⊗ᵢ (jX j (neg j)).2.some)) ⊗ᵢ ih.some) ≪≫
        α_ _ _ _⟩

  have undo : (Scheme.Modules.pullback bO).obj M ≅
      (Scheme.Modules.pullback eY.inv).obj ((Scheme.Modules.pullback eY.hom).obj ((Scheme.Modules.pullback bO).obj M)) :=
    ((Scheme.Modules.pullbackId _).app _).symm ≪≫
      (Scheme.Modules.pullbackCongr eY.inv_hom_id.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp eY.inv eY.hom).app _).symm
  exact ⟨PA ≪≫ undo ≪≫ (Scheme.Modules.pullback eY.inv).mapIso (PB ≪≫ (PC _).some) ≪≫ (PD _).some⟩

end S_ModularCurve_DRModelPackage_nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_nonempty_poincare_pullbackAlong_comp_iso_of_pullback_toDR_iso_of_sectionTwist (solution)
