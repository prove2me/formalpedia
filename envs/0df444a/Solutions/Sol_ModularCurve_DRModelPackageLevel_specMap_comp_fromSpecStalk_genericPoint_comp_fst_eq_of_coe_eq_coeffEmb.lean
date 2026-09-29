-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.specMap_comp_fromSpecStalk_genericPoint_comp_fst_eq_of_coe_eq_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8108cd67-8844-594c-a449-1263a2ae5b3e

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
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
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_specMap_comp_fromSpecStalk_genericPoint_comp_fst_eq_of_coe_eq_coeffEmb
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

private theorem fromSpecStalk_comp_eq_specMap_comp_of_mem
    {A : CommRingCat.{0}} {X Y : Scheme.{0}} (f : Y ⟶ X) (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (y : Y) (hy : f.base y ∈ ι ''ᵁ ⊤) :
    Y.fromSpecStalk y ≫ f =
      Spec.map ((Scheme.ΓSpecIso A).inv ≫ (ι.appIso ⊤).inv ≫ f.app (ι ''ᵁ ⊤) ≫ Y.presheaf.germ (f ⁻¹ᵁ (ι ''ᵁ ⊤)) y hy) ≫ ι := by
  obtain ⟨z, -, hz⟩ := hy

  have e : ι.base z = f.base y := hz
  have hsp : f.base y ⤳ ι.base z := e ▸ specializes_rfl
  have h1 : Y.fromSpecStalk y ≫ f = Spec.map (f.stalkMap y) ≫ X.fromSpecStalk (f.base y) :=
    (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  have h2 : X.fromSpecStalk (f.base y) = Spec.map (X.presheaf.stalkSpecializes hsp) ≫ X.fromSpecStalk (ι.base z) :=
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp).symm
  have h3 : X.fromSpecStalk (ι.base z) = Spec.map (inv (ι.stalkMap z)) ≫ (Spec A).fromSpecStalk z ≫ ι := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk ι, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  rw [h1, h2, h3, Spec.fromSpecStalk_eq]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  simp only [Category.assoc]
  congr 1

  have hzU : ι.base z ∈ ι ''ᵁ ⊤ := ⟨z, trivial, rfl⟩
  have e1 : (Spec A).presheaf.germ ⊤ z trivial ≫ inv (ι.stalkMap z) = (ι.appIso ⊤).inv ≫ X.presheaf.germ (ι ''ᵁ ⊤) (ι.base z) hzU := by
    rw [IsIso.comp_inv_eq, Category.assoc, Scheme.Hom.germ_stalkMap ι (ι ''ᵁ ⊤) z hzU, ← Category.assoc,
      Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res]
  rw [reassoc_of% e1, X.presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap f (ι ''ᵁ ⊤) y]

end

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) :
    Spec.map (CommRingCat.ofHom φ) ≫
        (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).fromSpecStalk
          (genericPoint ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))) ≫
        pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      Spec.map (CommRingCat.ofHom 𝔓.Meta.ffEquiv.symm.toRingHom) ≫ 𝔓.Meta.C.fromSpecStalk (genericPoint ↥𝔓.Meta.C) ≫
        𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ := by
  classical

  have hyO : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base
      (genericPoint ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))) ∈ (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤ :=
    ((genericPoint_spec ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))).mem_open_set_iff
      ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).isOpen).mpr
      (by simpa using hne)
  have hneM := 𝔓.Meta_chart_nonempty
  have hyM : (𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))).base
      (genericPoint ↥𝔓.Meta.C) ∈ (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤ :=
    ((genericPoint_spec ↥𝔓.Meta.C).mem_open_set_iff
      ((𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).isOpen).mpr (by simpa using hneM)
  rw [fromSpecStalk_comp_eq_specMap_comp_of_mem (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
    (IgusaScheme.ιFin (N₀ * q) q) _ hyO,
    fromSpecStalk_comp_eq_specMap_comp_of_mem (𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _) (IgusaScheme.ιFin (N₀ * q) q) _ hyM]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2

  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  have h1 := hφj a
  have h2 := 𝔓.Meta_pin a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  erw [h1, h2]

end S_ModularCurve_DRModelPackageLevel_specMap_comp_fromSpecStalk_genericPoint_comp_fst_eq_of_coe_eq_coeffEmb
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_specMap_comp_fromSpecStalk_genericPoint_comp_fst_eq_of_coe_eq_coeffEmb (solution)
