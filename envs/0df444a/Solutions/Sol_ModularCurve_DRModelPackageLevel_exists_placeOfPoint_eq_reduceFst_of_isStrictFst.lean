-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceFst_of_isStrictFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/230012fd-648b-565c-88b2-fffb271b2d6c

import Mathlib
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceFst_of_isStrictFst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (red : ↥A →+* κ) :
    letI : Algebra (R p) κ := (red.comp ρ).toAlgebra
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr κ red hα hβ)

      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C),
          (𝔓.efib κ (algebraMap (R p) κ)).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base (IsLocalRing.closedPoint κ) →
            (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C),
          (𝔓.efib κ (algebraMap (R p) κ)).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base
                (IsLocalRing.closedPoint κ) →
            (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y))

      (xW : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace xW))

      (t : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : barPt A ≫ t.1 = xW.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
      (tκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
      (_ : tκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ t.1) (_ : tκ ≫ pullback.snd _ _ = 𝟙 _),
      (∃ (P0 : closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C),
          (𝔓.efib κ (algebraMap (R p) κ) ≫ 𝔓.comp κ (algebraMap (R p) κ) 0).base P0.1 =
            tκ.base (IsLocalRing.closedPoint κ) ∧
          (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace xW)) ∧
      tκ.base (IsLocalRing.closedPoint κ) ∉ Set.range (𝔓.comp κ (algebraMap (R p) κ) 1).base := by
  letI : Algebra (R p) κ := (red.comp ρ).toAlgebra
  intro data hKr hα hβ P hGα hGβ xW hxW t ht tκ htκ₁ htκ₂
  classical

  set z : ↥(fibre (N₀ := N₀) (algebraMap (R p) κ)) := tκ.base (IsLocalRing.closedPoint κ) with hzdef
  have hefinv : ∀ y0 : ↥(fibre0 (N₀ := N₀) (algebraMap (R p) κ)), (𝔓.efib κ (algebraMap (R p) κ)).base ((inv (𝔓.efib κ (algebraMap (R p) κ))).base y0) = y0 := fun y0 => by
    show (inv (𝔓.efib κ (algebraMap (R p) κ)) ≫ 𝔓.efib κ (algebraMap (R p) κ)).base y0 = y0
    rw [IsIso.inv_hom_id]
    rfl

  have SEC : ∀ {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated g] (s : Spec (CommRingCat.of κ) ⟶ Y),
      s ≫ g = 𝟙 _ → s.base (IsLocalRing.closedPoint κ) ∈ closedPoints Y := by
    intro Y g _ s hs
    haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
    haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
    rw [mem_closedPoints_iff]
    have hr : Set.range s.base = {s.base (IsLocalRing.closedPoint κ)} := by
      ext x
      constructor
      · rintro ⟨pt, rfl⟩
        rw [Set.mem_singleton_iff, show pt = IsLocalRing.closedPoint κ from Subsingleton.elim _ _]
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hr]
    exact s.isClosedEmbedding.isClosed_range

  have INV : ∀ y0 : ↥(fibre0 (N₀ := N₀) (algebraMap (R p) κ)), y0 ∈ closedPoints (fibre0 (N₀ := N₀) (algebraMap (R p) κ)) →
      (inv (𝔓.efib κ (algebraMap (R p) κ))).base y0 ∈ closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C := by
    intro y0 hy0
    rw [mem_closedPoints_iff] at hy0 ⊢
    have himg : (inv (𝔓.efib κ (algebraMap (R p) κ))).base '' {y0} = {(inv (𝔓.efib κ (algebraMap (R p) κ))).base y0} := Set.image_singleton
    rw [← himg]
    exact (inv (𝔓.efib κ (algebraMap (R p) κ))).isClosedEmbedding.isClosedMap _ hy0

  haveI : IsSeparated (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) := by
    haveI := DRModelPackageLevel.isProper_fibre 𝔓 (algebraMap (R p) κ); infer_instance
  haveI : IsSeparated (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) := by
    haveI := DRModelPackageLevel.isProper_fibre0 𝔓 (algebraMap (R p) κ); infer_instance
  have CLOSED : ∀ (i : Fin 2) (y0 : ↥(fibre0 (N₀ := N₀) (algebraMap (R p) κ))), (𝔓.comp κ (algebraMap (R p) κ) i).base y0 = z →
      (inv (𝔓.efib κ (algebraMap (R p) κ))).base y0 ∈ closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C := by
    intro i y0 hy0
    apply INV

    have hz : z ∈ closedPoints (fibre (N₀ := N₀) (algebraMap (R p) κ)) := SEC _ tκ htκ₂
    rw [mem_closedPoints_iff] at hz ⊢
    haveI := 𝔓.comp_isClosedImmersion κ (algebraMap (R p) κ) i
    have hpre : (𝔓.comp κ (algebraMap (R p) κ) i).base ⁻¹' {z} = {y0} := by
      ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hy; exact (𝔓.comp κ (algebraMap (R p) κ) i).isClosedEmbedding.injective (hy.trans hy0.symm)
      · rintro rfl; exact hy0
    rw [← hpre]
    exact hz.preimage (𝔓.comp κ (algebraMap (R p) κ) i).base.hom.continuous
  have CLOSEDπ : (inv (𝔓.efib κ (algebraMap (R p) κ))).base ((fibreMap0 𝔓.π (algebraMap (R p) κ)).base z) ∈ closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C := by
    apply INV
    have e : (fibreMap0 𝔓.π (algebraMap (R p) κ)).base z = (tκ ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base (IsLocalRing.closedPoint κ) := rfl
    rw [e]
    refine SEC (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) _ ?_
    rw [Category.assoc, DRLevel.fibreMap0_snd, htκ₂]
  have CLOSEDπw : (inv (𝔓.efib κ (algebraMap (R p) κ))).base ((fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base z) ∈
      closedPoints (𝔓.Mfib κ (algebraMap (R p) κ)).C := by
    apply INV
    have e : (fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base z =
        (tκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base (IsLocalRing.closedPoint κ) := rfl
    rw [e]
    refine SEC (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) _ ?_
    rw [Category.assoc, Category.assoc, DRLevel.fibreMap0_snd, DRLevel.fibreMap_snd, htκ₂]

  have comp_w' : 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) = 𝔓.comp κ (algebraMap (R p) κ) 0 :=
    𝔓.comp1_fibreMap_w (algebraMap (R p) κ)

  have FROB : ∀ Q : Place κ ↥(modularFunctionFieldC κ N₀), arithFrobC p κ N₀ • Q = frobOnPlacesGeomLevel κ N₀ data hKr Q :=
    fun Q => ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel p κ N₀ data hKr Q

  have hGa : (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint ⟨_, CLOSEDπ⟩ = P.reduceFst (𝔓.Meta.pointEquivPlace xW) :=
    hGα xW t ht tκ htκ₁ htκ₂ (Or.inl hxW) ⟨_, CLOSEDπ⟩ (by rw [hefinv]; rfl)
  have hGb : (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint ⟨_, CLOSEDπw⟩ = P.reduceSnd (𝔓.Meta.pointEquivPlace xW) :=
    hGβ xW t ht tκ htκ₁ htκ₂ (Or.inl hxW) ⟨_, CLOSEDπw⟩ (by rw [hefinv]; rfl)

  have hnot1 : z ∉ Set.range (𝔓.comp κ (algebraMap (R p) κ) 1).base := by
    rintro ⟨z1, hz1⟩
    have hc1 := CLOSED 1 z1 hz1
    obtain ⟨h1, hplace1⟩ := 𝔓.comp1_pi_place κ (algebraMap (R p) κ) ⟨_, hc1⟩

    have e1 : (𝔓.efib κ (algebraMap (R p) κ) ≫ 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base ((inv (𝔓.efib κ (algebraMap (R p) κ))).base z1) =
        (fibreMap0 𝔓.π (algebraMap (R p) κ)).base z := by
      show (fibreMap0 𝔓.π (algebraMap (R p) κ)).base ((𝔓.comp κ (algebraMap (R p) κ) 1).base ((𝔓.efib κ (algebraMap (R p) κ)).base ((inv (𝔓.efib κ (algebraMap (R p) κ))).base z1))) = _
      rw [hefinv, hz1]
    have hF : P.reduceFst (𝔓.Meta.pointEquivPlace xW) = arithFrobC p κ N₀ • (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint ⟨_, hc1⟩ := by
      rw [← hGa, ← hplace1]
      congr 1
      apply Subtype.ext
      show (inv (𝔓.efib κ (algebraMap (R p) κ))).base _ = (inv (𝔓.efib κ (algebraMap (R p) κ))).base _
      rw [e1]

    have e2 : (fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ) ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base z = z1 := by
      show (fibreMap0 𝔓.π (algebraMap (R p) κ)).base ((fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ)).base z) = z1
      rw [← hz1, show (fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ)).base ((𝔓.comp κ (algebraMap (R p) κ) 1).base z1) =
        (𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) κ)).base z1 from rfl, comp_w',
        show (fibreMap0 𝔓.π (algebraMap (R p) κ)).base ((𝔓.comp κ (algebraMap (R p) κ) 0).base z1) = (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base z1 from rfl,
        𝔓.comp_pi]
      rfl
    have hS : P.reduceSnd (𝔓.Meta.pointEquivPlace xW) = (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint ⟨_, hc1⟩ := by
      rw [← hGb]
      congr 1
      apply Subtype.ext
      show (inv (𝔓.efib κ (algebraMap (R p) κ))).base _ = (inv (𝔓.efib κ (algebraMap (R p) κ))).base _
      rw [e2]

    apply hxW.2
    have hkey : frobOnPlacesGeomLevel κ N₀ data hKr (frobOnPlacesGeomLevel κ N₀ data hKr ((𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint ⟨_, hc1⟩)) =
        (𝔓.Mfib κ (algebraMap (R p) κ)).placeOfPoint ⟨_, hc1⟩ := by
      have h := hxW.1
      rw [hF, FROB, hS] at h
      exact h
    rw [hF, FROB, hkey]

  obtain ⟨z0, hz0⟩ := (𝔓.comp_jointly_surjective κ (algebraMap (R p) κ) z).resolve_right hnot1
  refine ⟨⟨⟨_, CLOSED 0 z0 hz0⟩, ?_, ?_⟩, hnot1⟩
  · show (𝔓.comp κ (algebraMap (R p) κ) 0).base ((𝔓.efib κ (algebraMap (R p) κ)).base ((inv (𝔓.efib κ (algebraMap (R p) κ))).base z0)) = z
    rw [hefinv, hz0]
  · rw [← hGa]
    congr 1
    apply Subtype.ext
    show (inv (𝔓.efib κ (algebraMap (R p) κ))).base z0 = (inv (𝔓.efib κ (algebraMap (R p) κ))).base ((fibreMap0 𝔓.π (algebraMap (R p) κ)).base z)
    rw [← hz0, show (fibreMap0 𝔓.π (algebraMap (R p) κ)).base ((𝔓.comp κ (algebraMap (R p) κ) 0).base z0) = (𝔓.comp κ (algebraMap (R p) κ) 0 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ)).base z0 from rfl,
      𝔓.comp_pi]
    rfl

end S_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceFst_of_isStrictFst
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceFst_of_isStrictFst (solution)
