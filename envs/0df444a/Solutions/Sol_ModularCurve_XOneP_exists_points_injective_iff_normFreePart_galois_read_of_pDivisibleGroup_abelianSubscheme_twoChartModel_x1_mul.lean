-- Prove2me | solution 1 for ModularCurve.XOneP.exists_points_injective_iff_normFreePart_galois_read_of_pDivisibleGroup_abelianSubscheme_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/736b83b5-c55e-51ad-b065-0590c653df55

import Mathlib
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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_points_injective_iff_normFreePart_galois_read_of_pDivisibleGroup_abelianSubscheme_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

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

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

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

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

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

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)

    (h𝒜cl : IsClosedImmersion ι.1)

    (h𝒜pr : IsProper a) (h𝒜sm : Smooth a)
    (h𝒜conn : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s))

    (h𝒜grp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι)))

    (h𝒜gen : ∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1)

    (h𝒜hecke : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : RingHom.ker πk = IsLocalRing.maximalIdeal ↥Pl)

    (L𝒜 : GoodReductionJacobian.RelativeGroupLaw A a) (hL𝒜c : L𝒜.IsCommutative)
    (hL𝒜ι : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s a),
      NeronModelInfra.schemeHomOverComp (L𝒜.mul s x y) ι =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι))
    (h : ℕ) (GA : PDivisibleGroup A p h)
    (ιGpts : GA.Points (AlgebraicClosure ℚ) →+ L𝒜.AlgPoints hL𝒜c (AlgebraicClosure ℚ))
    (ιG : ∀ v : ℕ, Spec (CommRingCat.of (GA.level v)) ⟶ 𝒜)
    (hPinj : Function.Injective ιGpts)
    (hPgal : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[A] (AlgebraicClosure ℚ)) (x : GA.Points (AlgebraicClosure ℚ)), ιGpts (σ • x) = σ • ιGpts x)
    (hPtors : ∀ (e : L𝒜.AlgPoints hL𝒜c (AlgebraicClosure ℚ)) (n : ℕ), ((p ^ n : ℕ) : ℤ) • e = 0 → e ∈ ιGpts.range)
    (hS1 : ∀ v : ℕ, ιG v ≫ a = Spec.map (CommRingCat.ofHom (algebraMap A (GA.level v))))
    (hS2 : ∀ v : ℕ, IsClosedImmersion (ιG v))
    (hS3 : ∀ v : ℕ, ιG v ≫ L𝒜.schemeNsmul (p ^ v) = (ιG v ≫ a) ≫ (L𝒜.one (𝟙 (Spec (CommRingCat.of A)))).1)
    (hS4 : ∀ (v : ℕ) (x : GA.Point (AlgebraicClosure ℚ) v),
          (GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint (ιGpts (GA.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
            Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : GA.level v →ₐ[A] (AlgebraicClosure ℚ)) : GA.level v →+* (AlgebraicClosure ℚ))) ≫ ιG v)
    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra A B] (x y : GA.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : GA.level v →ₐ[A] B) : GA.level v →+* B)) ≫ ιG v) ≫ a =
            Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : GA.level v →ₐ[A] B) : GA.level v →+* B)) ≫ ιG v) ≫ a =
            Spec.map (CommRingCat.ofHom (algebraMap A B))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : GA.level v →ₐ[A] B) : GA.level v →+* B)) ≫ ιG v =
            (L𝒜.mul (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟨_, hx⟩ ⟨_, hy⟩).1) :
    ∃ Δ : GA.Points (AlgebraicClosure ℚ) →+ ModularCurve.JOne (M * p),

      Function.Injective Δ ∧

      (∀ (v : ℕ) (y : ModularCurve.JOne (M * p)),
        ((p ^ v) • y = 0 ∧ y ∈ ModularCurve.normFreePartAt (M * p) p) ↔
        ∃ x : GA.Point (AlgebraicClosure ℚ) v, Δ (GA.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y) ∧

      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[A] AlgebraicClosure ℚ),
        (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : GA.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z) ∧

      (∀ (v : ℕ) (x : GA.Point (AlgebraicClosure ℚ) v),
        (gpts (Δ (GA.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : GA.level v →ₐ[A] (AlgebraicClosure ℚ)) : GA.level v →+* (AlgebraicClosure ℚ))) ≫ ιG v ≫ ι.1) := by
  classical

  haveI hmono : Mono ι.1 := inferInstance
  let LD := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some

  let ιD : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a → SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase := fun Y =>
    NeronModelInfra.schemeHomOverComp Y ι
  have ιD_val : ∀ Y, (ιD Y).1 = Y.1 ≫ ι.1 := fun Y => rfl
  have ιD_injective : Function.Injective ιD := by
    intro Y₁ Y₂ hY
    apply Subtype.ext
    have h1 := congrArg Subtype.val hY
    rw [ιD_val, ιD_val] at h1
    exact (cancel_mono ι.1).mp h1

  let δf : L𝒜.AlgPoints hL𝒜c (AlgebraicClosure ℚ) → ModularCurve.JOne (M * p) := fun e =>
    gpts.symm (ιD (GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint e))
  have hδf : ∀ e, gpts (δf e) = ιD (GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint e) := fun e =>
    gpts.apply_symm_apply _
  have δf_add : ∀ e₁ e₂, δf (e₁ + e₂) = δf e₁ + δf e₂ := by
    intro e₁ e₂
    apply gpts.injective
    rw [hgadd, hδf, hδf, hδf, GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_add]
    exact hL𝒜ι _ _ _
  let δ' : L𝒜.AlgPoints hL𝒜c (AlgebraicClosure ℚ) →+ ModularCurve.JOne (M * p) := AddMonoidHom.mk' δf δf_add
  have hδ' : ∀ e, gpts (δ' e) = ιD (GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint e) := hδf
  have δ'_injective : Function.Injective δ' := fun e₁ e₂ h12 =>
    GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_injective (ιD_injective (gpts.symm.injective h12))

  let Δ : GA.Points (AlgebraicClosure ℚ) →+ ModularCurve.JOne (M * p) := δ'.comp ιGpts
  have hΔ : ∀ z, Δ z = δ' (ιGpts z) := fun z => rfl
  refine ⟨Δ, ?_, ?_, ?_, ?_⟩
  ·
    exact δ'_injective.comp hPinj
  ·
    intro v y
    constructor
    · rintro ⟨hy0, hyA⟩

      obtain ⟨Y, hY⟩ := (h𝒜gen y).mp hyA
      let e : L𝒜.AlgPoints hL𝒜c (AlgebraicClosure ℚ) := GoodReductionJacobian.RelativeGroupLaw.AlgPoints.ofPoint Y
      have he : δ' e = y := by
        apply gpts.injective
        rw [hδ']
        exact Subtype.ext hY

      have hev : ((p ^ v : ℕ) : ℤ) • e = 0 := by
        apply δ'_injective
        rw [map_zsmul, he, map_zero, natCast_zsmul]
        exact hy0
      obtain ⟨z, hz⟩ := hPtors e v hev
      have hzv : (p ^ v) • z = 0 := by
        apply hPinj
        rw [map_nsmul, hz, map_zero, ← natCast_zsmul]
        exact hev

      obtain ⟨w, x', rfl⟩ := PDivisibleGroup.Points.exists_mkAdd (G := GA) (L := AlgebraicClosure ℚ) z
      have hx : ∃ x : GA.Point (AlgebraicClosure ℚ) v, GA.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x) = GA.pointsMkAdd (AlgebraicClosure ℚ) w (Additive.ofMul x') := by
        rcases le_total w v with hwv | hvw
        · exact ⟨GA.pointInclLE (AlgebraicClosure ℚ) hwv x', by rw [PDivisibleGroup.pointsMkAdd_pointInclLE]⟩
        · have hpow : x' ^ (p ^ v) = 1 := by
            apply Additive.ofMul.injective
            apply PDivisibleGroup.pointsMkAdd_injective (G := GA) (L := AlgebraicClosure ℚ) w
            rw [ofMul_pow, map_nsmul, hzv, ofMul_one, map_zero]
          obtain ⟨x, hx⟩ := PDivisibleGroup.exists_pointInclLE_eq_of_pow_eq_one (G := GA) (L := AlgebraicClosure ℚ) hvw x' hpow
          exact ⟨x, by rw [← hx, PDivisibleGroup.pointsMkAdd_pointInclLE]⟩
      obtain ⟨x, hx⟩ := hx
      refine ⟨x, ?_⟩
      rw [hΔ, hx, hz, he]
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← map_nsmul, PDivisibleGroup.nsmul_pointsMkAdd_eq_zero, map_zero]
      · rw [h𝒜gen]
        refine ⟨GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint (ιGpts (GA.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))), ?_⟩
        rw [hΔ, hδ']
        rfl
  ·
    intro τ₀ τ' hτ z

    have hτL : ∀ l : L, τ₀ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l := by
      intro l
      rw [← hτ]
      obtain ⟨⟨num, den⟩, hl⟩ := IsLocalization.surj (nonZeroDivisors A) l
      have hden : algebraMap A (AlgebraicClosure ℚ) den ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ)]
        exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors den.2)
      have hl' : algebraMap L (AlgebraicClosure ℚ) l * algebraMap A (AlgebraicClosure ℚ) den = algebraMap A (AlgebraicClosure ℚ) num := by
        rw [IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ), IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ), ← map_mul, hl]
      have h1 : τ' (algebraMap L (AlgebraicClosure ℚ) l) * algebraMap A (AlgebraicClosure ℚ) den = algebraMap A (AlgebraicClosure ℚ) num := by
        rw [← τ'.commutes den, ← map_mul, hl', τ'.commutes]
      exact mul_right_cancel₀ hden (h1.trans hl'.symm)
    have hring : ((τ' : AlgebraicClosure ℚ →ₐ[A] AlgebraicClosure ℚ).toRingHom) = (τ₀.toRingEquiv.toRingHom) := RingHom.ext fun x => hτ x
    apply gpts.injective
    apply Subtype.ext
    rw [hτpts τ₀ 1 (fun l => by rw [hτL]; simp), inv_one, hτ1, Category.comp_id, hΔ, hΔ, hδ', hδ', hPgal, ιD_val, ιD_val,
      GoodReductionJacobian.RelativeGroupLaw.AlgPoints.toPoint_smul_coe, hring, Category.assoc]
  ·
    intro v x
    rw [hΔ, hδ', ιD_val, hS4, Category.assoc]

end S_ModularCurve_XOneP_exists_points_injective_iff_normFreePart_galois_read_of_pDivisibleGroup_abelianSubscheme_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_points_injective_iff_normFreePart_galois_read_of_pDivisibleGroup_abelianSubscheme_twoChartModel_x1_mul (solution)
