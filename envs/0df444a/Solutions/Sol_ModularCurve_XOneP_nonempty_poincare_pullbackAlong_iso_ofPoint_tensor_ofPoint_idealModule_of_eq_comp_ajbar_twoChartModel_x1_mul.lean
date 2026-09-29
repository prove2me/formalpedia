-- Prove2me | solution 1 for ModularCurve.XOneP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6f374fc7-5597-563d-ab54-10b30486a4f4

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (ybar : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hybar : ybar.1 = y.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (a : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase) (ha : a.1 = y.1 ≫ ajbar) :
    Nonempty ((hrep.some.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ybar.1 ybar.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ) ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (specMap A (AlgebraicClosure ℚ) ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) := by
  classical

  let Xm := ModularCurve.TwoChart.modelTo A (↥K) j
  let Qb := AlgebraicClosure ℚ
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of A) := specMap A Qb
  let sL : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of L) := specMap L Qb
  let XL := baseChange A Xm L
  let DL := D.baseChange L
  let h := hrep.some
  let P := h.poincare
  let Pb := hDL.poincare
  haveI := hsmL

  have htQ : sL ≫ specMap A L = tQ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hysnd : y.1 ≫ eη ≫ pullback.snd Xm tQ = 𝟙 _ := by rw [heη]; exact y.2

  let x : SchemeHomOver sL XL := ⟨y.1 ≫ eη ≫ kL, by
    show (y.1 ≫ eη ≫ kL) ≫ pullback.snd Xm (specMap A L) = sL
    rw [Category.assoc, Category.assoc, hkL₂, ← Category.assoc eη, ← Category.assoc, hysnd, Category.id_comp]⟩
  let v : SchemeHomOver sL DL.toBase :=
    ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩
  let fstD : SchemeHomOver (DL.toBase ≫ specMap A L) D.toBase := ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩

  let φ : pullback Xm tQ ⟶ pullback XL sL := pullback.lift kL (pullback.snd Xm tQ) hkL₂
  have hφfst : φ ≫ pullback.fst XL sL = kL := pullback.lift_fst _ _ _
  have hφsnd : φ ≫ pullback.snd XL sL = pullback.snd Xm tQ := pullback.lift_snd _ _ _
  let ψ : pullback XL sL ⟶ pullback Xm tQ :=
    pullback.lift (pullback.fst XL sL ≫ pullback.fst Xm (specMap A L)) (pullback.snd XL sL) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, htQ])
  have hψfst : ψ ≫ pullback.fst Xm tQ = pullback.fst XL sL ≫ pullback.fst Xm (specMap A L) := pullback.lift_fst _ _ _
  have hψsnd : ψ ≫ pullback.snd Xm tQ = pullback.snd XL sL := pullback.lift_snd _ _ _
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψfst, ← Category.assoc, hφfst, hkL₁, Category.id_comp]
    · rw [Category.assoc, hψsnd, hφsnd, Category.id_comp]
  have hψkL : ψ ≫ kL = pullback.fst XL sL := by
    apply pullback.hom_ext
    · rw [Category.assoc, hkL₁, hψfst]
    · rw [Category.assoc, hkL₂, ← Category.assoc, hψsnd, pullback.condition]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφfst, hψkL, Category.id_comp]
    · rw [Category.assoc, hφsnd, hψsnd, Category.id_comp]
  haveI hφiso : IsIso φ := ⟨ψ, hφψ, hψφ⟩

  have hchain : φ ≫ baseChangeSnd XL v ≫ (BaseChange.κ Xm L DL.toBase).hom ≫ baseChangeSnd Xm fstD = baseChangeSnd Xm a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        ← Category.assoc (baseChangeSnd XL v), BaseChange.baseChangeSnd_fst', ← Category.assoc, hφfst, hkL₁,
        BaseChange.baseChangeSnd_fst']
    · rw [Category.assoc, Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc (BaseChange.κ Xm L DL.toBase).hom,
        BaseChange.κ_hom_snd, ← Category.assoc (baseChangeSnd XL v), BaseChange.baseChangeSnd_snd', Category.assoc,
        ← Category.assoc φ, hφsnd, BaseChange.baseChangeSnd_snd', ha, hajbar]
      simp only [v, x, fstD, Category.assoc]
      rfl
  obtain ⟨ePL⟩ := hPL
  have e1 : (P.pullbackAlong a).L ≅ (Scheme.Modules.pullback φ).obj ((Pb.pullbackAlong v).L) := by
    refine (Scheme.Modules.pullbackCongr hchain.symm).app P.L ≪≫
      ((Scheme.Modules.pullbackComp φ (baseChangeSnd XL v ≫ (BaseChange.κ Xm L DL.toBase).hom ≫ baseChangeSnd Xm fstD)).app P.L).symm ≪≫
      (Scheme.Modules.pullback φ).mapIso ?_
    refine ((Scheme.Modules.pullbackComp (baseChangeSnd XL v) ((BaseChange.κ Xm L DL.toBase).hom ≫ baseChangeSnd Xm fstD)).app P.L).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd XL v)).mapIso ?_
    exact ((Scheme.Modules.pullbackComp (BaseChange.κ Xm L DL.toBase).hom (baseChangeSnd Xm fstD)).app P.L).symm ≪≫ ePL.symm

  obtain ⟨e2⟩ := hajL Qb sL x

  haveI hsmQ : SmoothOfRelativeDimension 1 (pullback.snd Xm tQ) := by
    have hsndi : inv eη ≫ Mη.toBase = pullback.snd Xm tQ := by rw [← heη, IsIso.inv_hom_id_assoc]
    rw [← hsndi]; exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (inv eη ≫ Mη.toBase))
  haveI : IsSeparated Xm := inferInstance

  have hεLover : (sL ≫ (sectionBaseChange L ε).1) ≫ XL = sL :=
    (Category.assoc _ _ _).trans ((congrArg (sL ≫ ·) (sectionBaseChange L ε).2).trans (Category.comp_id sL))
  have hεover : (tQ ≫ ε.1) ≫ Xm = tQ :=
    (Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) ε.2).trans (Category.comp_id _))
  have hp : graphOver Xm ybar.1 ybar.2 ≫ φ = graphOver XL x.1 x.2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφfst, graphOver_fst]
      apply pullback.hom_ext
      · rw [Category.assoc, hkL₁, graphOver_fst, hybar]
        show _ = (y.1 ≫ eη ≫ kL) ≫ _
        rw [Category.assoc, Category.assoc, hkL₁]
      · rw [Category.assoc, hkL₂, ← Category.assoc, graphOver_snd, Category.id_comp]
        show _ = (y.1 ≫ eη ≫ kL) ≫ _
        rw [Category.assoc, Category.assoc, hkL₂, ← Category.assoc eη, ← Category.assoc, hysnd, Category.id_comp]
    · rw [Category.assoc, hφsnd, graphOver_snd, graphOver_snd]
  have hq : graphOver Xm (tQ ≫ ε.1) hεover ≫ φ = graphOver XL (sL ≫ (sectionBaseChange L ε).1) hεLover := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφfst, graphOver_fst]
      apply pullback.hom_ext
      · rw [Category.assoc, hkL₁, graphOver_fst, Category.assoc, sectionBaseChange_coe_fst, ← Category.assoc sL, htQ]
      · rw [Category.assoc, hkL₂, ← Category.assoc, graphOver_snd, Category.id_comp, Category.assoc,
          sectionBaseChange_coe_snd, Category.comp_id]
    · rw [Category.assoc, hφsnd, graphOver_snd, graphOver_snd]
  have hIx : (graphOver XL x.1 x.2).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd XL sL) _ (graphOver_snd XL x.1 x.2)
  have hIy : (graphOver Xm ybar.1 ybar.2).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd Xm tQ) _ (graphOver_snd Xm ybar.1 ybar.2)
  have hIεL : (graphOver XL (sL ≫ (sectionBaseChange L ε).1) hεLover).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd XL sL) _ (graphOver_snd XL _ hεLover)
  have hIε : (graphOver Xm (tQ ≫ ε.1) hεover).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd Xm tQ) _ (graphOver_snd Xm _ hεover)
  have kO := AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso φ
    (graphOver XL x.1 x.2) (graphOver Xm ybar.1 ybar.2) hp hIx hIy 1
  have kI := AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso φ
    (graphOver XL (sL ≫ (sectionBaseChange L ε).1) hεLover) (graphOver Xm (tQ ≫ ε.1) hεover) hq hIεL hIε 1
  rw [pow_one, pow_one] at kO kI
  obtain ⟨eO⟩ := kO.1
  obtain ⟨eI⟩ := kI.2

  exact ⟨e1 ≪≫ (Scheme.Modules.pullback φ).mapIso e2 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eO ⊗ᵢ eI)⟩

end S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul (solution)
