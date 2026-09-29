-- Prove2me | solution 1 for ModularCurve.XOneP.exists_pts_comp_fst_eq_and_proj_eq_zero_of_pullback_poincare_pullbackAlong_iso_unit_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/369c3edf-a0c6-56de-910e-a9a7a2d78fe7

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
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_pts_comp_fst_eq_and_proj_eq_zero_of_pullback_poincare_pullbackAlong_iso_unit_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

universe u

namespace Ws5B13H2

theorem transport_eq {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (k : Type u) [CommRing k] [Algebra R k] (D : RelativePic0Designation R c)
    {T : Scheme.{u}} (ρ' : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver ρ' D.toBase)
    (π : Spec (CommRingCat.of k) ⟶ T)
    (jk : pullback c (specMap R k) ⟶ pullback c ρ')
    (hjk₁ : jk ≫ pullback.fst _ _ = pullback.fst _ _)
    (hjk₂ : jk ≫ pullback.snd _ _ = pullback.snd _ _ ≫ π)
    (zk : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hzk : zk.1 ≫ pullback.fst D.toBase (specMap R k) = π ≫ z.1)
    {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of k)) (f : C' ⟶ pullback c (specMap R k))
    (hf : f ≫ baseChange R c k = c') :
    curveChange f hf (𝟙 _) ≫ baseChangeSnd (baseChange R c k) zk ≫
        (BaseChange.κ c k (D.baseChange k).toBase).hom ≫
        baseChangeSnd c (⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩ :
          SchemeHomOver ((D.baseChange k).toBase ≫ specMap R k) D.toBase) =
      pullback.fst c' (𝟙 _) ≫ f ≫ jk ≫ baseChangeSnd c z := by
  have hf' : f ≫ pullback.snd c (specMap R k) = c' := hf
  apply pullback.hom_ext
  · simp only [curveChange, baseChangeSnd, BaseChange.κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_fst, hjk₁]
  · simp only [curveChange, baseChangeSnd, BaseChange.κ, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp,
      pullbackLeftPullbackSndIso_hom_snd_assoc, reassoc_of% hjk₂,
      reassoc_of% hf', hzk, pullback.condition_assoc]

noncomputable def transportIso {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (k : Type u) [CommRing k] [Algebra R k] (D : RelativePic0Designation R c)
    (Pc : RigidifiedLineBundle c ε D.toBase)
    (Pk : RigidifiedLineBundle (baseChange R c k) (sectionBaseChange k ε) (D.baseChange k).toBase)
    (eP : Pk.L ≅ (BaseChange.ofR c ε k (Pc.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L)
    {T : Scheme.{u}} (ρ' : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver ρ' D.toBase)
    (π : Spec (CommRingCat.of k) ⟶ T)
    (jk : pullback c (specMap R k) ⟶ pullback c ρ')
    (hjk₁ : jk ≫ pullback.fst _ _ = pullback.fst _ _)
    (hjk₂ : jk ≫ pullback.snd _ _ = pullback.snd _ _ ≫ π)
    (zk : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hzk : zk.1 ≫ pullback.fst D.toBase (specMap R k) = π ≫ z.1)
    {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of k)) (f : C' ⟶ pullback c (specMap R k))
    (hf : f ≫ baseChange R c k = c') :
    (Scheme.Modules.pullback (curveChange f hf (𝟙 _))).obj (Pk.pullbackAlong zk).L ≅
      (Scheme.Modules.pullback (pullback.fst c' (𝟙 _))).obj
        ((Scheme.Modules.pullback (f ≫ jk)).obj (Pc.pullbackAlong z).L) :=
  let cc := curveChange f hf (𝟙 (Spec (CommRingCat.of k)))
  let bz := baseChangeSnd (baseChange R c k) zk
  let κh := (BaseChange.κ c k (D.baseChange k).toBase).hom
  let bσ := baseChangeSnd c (⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩ :
    SchemeHomOver ((D.baseChange k).toBase ≫ specMap R k) D.toBase)
  let p1 := pullback.fst c' (𝟙 (Spec (CommRingCat.of k)))
  (Scheme.Modules.pullback cc).mapIso ((Scheme.Modules.pullback bz).mapIso eP) ≪≫
    (Scheme.Modules.pullback cc).mapIso ((Scheme.Modules.pullback bz).mapIso
      ((Scheme.Modules.pullbackComp κh bσ).app Pc.L)) ≪≫
    (Scheme.Modules.pullback cc).mapIso ((Scheme.Modules.pullbackComp bz (κh ≫ bσ)).app Pc.L) ≪≫
    (Scheme.Modules.pullbackComp cc (bz ≫ κh ≫ bσ)).app Pc.L ≪≫
    (Scheme.Modules.pullbackCongr
      ((transport_eq c k D ρ' z π jk hjk₁ hjk₂ zk hzk c' f hf).trans (by rw [Category.assoc]))).app Pc.L ≪≫
    ((Scheme.Modules.pullbackComp p1 ((f ≫ jk) ≫ baseChangeSnd c z)).app Pc.L).symm ≪≫
    (Scheme.Modules.pullback p1).mapIso ((Scheme.Modules.pullbackComp (f ≫ jk) (baseChangeSnd c z)).app Pc.L).symm

noncomputable def poincarePostCompPullbackHomIso {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (g : SchemeHomOver t D.toBase) :
    (h'.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') g)).L ≅
      (Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong g).L :=
  (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
    (h.poincare.pullbackCurvePullbackAlongIso f hf hε _)

theorem eq_zero_of_poincare_iso_unit {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicCondition c ε} {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε P D)
    {J : Type*} [AddCommGroup J] (φ : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    (hadd : ∀ a b : J, Nonempty ((h.poincare.pullbackAlong (φ (a + b))).L ≅
      (h.poincare.pullbackAlong (φ a)).L ⊗ (h.poincare.pullbackAlong (φ b)).L))
    (x : J) (hx : Nonempty ((h.poincare.pullbackAlong (φ x)).L ≅
      SheafOfModules.unit (pullback c (𝟙 (Spec (CommRingCat.of R)))).ringCatSheaf)) : x = 0 := by
  obtain ⟨e⟩ := hx
  have key : φ (x + x) = φ x :=
    h.ext_of_iso (𝟙 _) _ _ ⟨(hadd x x).some ≪≫ (e ⊗ᵢ e) ≪≫ (λ_ _) ≪≫ e.symm⟩
  exact add_left_cancel ((φ.injective key).trans (add_zero x).symm)

noncomputable def isoUnitOfRigidify {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (hσq : σ ≫ q = 𝟙 T)
    {N Q : P.Modules} (eN : N ≅ SheafOfModules.unit P.ringCatSheaf) (eQ : Q ≅ Scheme.Modules.rigidify σ q N)
    (eR : (Scheme.Modules.pullback σ).obj Q ≅ SheafOfModules.unit T.ringCatSheaf) :
    Q ≅ SheafOfModules.unit P.ringCatSheaf := by
  let E : T.Modules := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj (SheafOfModules.unit P.ringCatSheaf))
  have e1 : Q ≅ (Scheme.Modules.pullback q).obj E :=
    eQ ≪≫ Scheme.Modules.rigidifyMapIso σ q eN ≪≫ (λ_ _)
  have e2 : E ≅ SheafOfModules.unit T.ringCatSheaf :=
    ((Scheme.Modules.pullbackId T).app E).symm ≪≫ (Scheme.Modules.pullbackCongr hσq.symm).app E ≪≫
      ((Scheme.Modules.pullbackComp σ q).app E).symm ≪≫ (Scheme.Modules.pullback σ).mapIso e1.symm ≪≫ eR
  exact e1 ≪≫ (Scheme.Modules.pullback q).mapIso e2 ≪≫ Scheme.Modules.pullbackUnitIso q

end Ws5B13H2

open Ws5B13H2 in

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

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

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

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (jk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hjk₁ : jk ≫ pullback.fst _ _ = pullback.fst _ _)
    (hjk₂ : jk ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk))

    (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (hcomp₁ : Nonempty ((Scheme.Modules.pullback (i₁.1 ≫ jk)).obj (hrep.some.poincare.pullbackAlong z).L ≅ SheafOfModules.unit C₁.ringCatSheaf))
    (hcomp₂ : Nonempty ((Scheme.Modules.pullback (i₂.1 ≫ jk)).obj (hrep.some.poincare.pullbackAlong z).L ≅ SheafOfModules.unit C₂.ringCatSheaf)) :
    ∃ y : G.J0s,
      (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 ∧ G.proj y = 0 := by
  classical

  have hψ : Spec.map (CommRingCat.ofHom πk) ≫ Spec.map (CommRingCat.ofHom ρ) = specMap A k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]
  let zk : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase :=
    ⟨pullback.lift (Spec.map (CommRingCat.ofHom πk) ≫ z.1) (𝟙 _)
        (by rw [Category.assoc, z.2, hψ, Category.id_comp]), pullback.lift_snd _ _ _⟩
  have hzk : zk.1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 :=
    pullback.lift_fst _ _ _
  obtain ⟨y, hy⟩ : ∃ y : G.J0s, pts y = zk := ⟨pts.symm zk, pts.apply_symm_apply zk⟩
  refine ⟨y, ?_, ?_⟩
  · rw [hy]; exact hzk

  have eN₁ : (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).obj (hreps.poincare.pullbackAlong zk).L ≅
      SheafOfModules.unit (pullback c₁ (𝟙 _)).ringCatSheaf :=
    transportIso (ModularCurve.TwoChart.modelTo A (↥K) j) ε k D hrep.some.poincare hreps.poincare hPk.some
      (Spec.map (CommRingCat.ofHom ρ)) z (Spec.map (CommRingCat.ofHom πk)) jk hjk₁ hjk₂ zk hzk c₁ i₁.1 i₁.2 ≪≫
    (Scheme.Modules.pullback _).mapIso hcomp₁.some ≪≫ Scheme.Modules.pullbackUnitIso _
  have eN₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 (𝟙 _))).obj (hreps.poincare.pullbackAlong zk).L ≅
      SheafOfModules.unit (pullback c₂ (𝟙 _)).ringCatSheaf :=
    transportIso (ModularCurve.TwoChart.modelTo A (↥K) j) ε k D hrep.some.poincare hreps.poincare hPk.some
      (Spec.map (CommRingCat.ofHom ρ)) z (Spec.map (CommRingCat.ofHom πk)) jk hjk₁ hjk₂ zk hzk c₂ i₂.1 i₂.2 ≪≫
    (Scheme.Modules.pullback _).mapIso hcomp₂.some ≪≫ Scheme.Modules.pullbackUnitIso _

  have hproj₁ := (hproj y).1
  rw [hy] at hproj₁
  have e₁ : Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI (G.proj y).1)).L ≅ SheafOfModules.unit (pullback c₁ (𝟙 _)).ringCatSheaf) := by
    rw [hproj₁]
    exact ⟨poincarePostCompPullbackHomIso i₁.1 i₁.2 hε₁ hreps hrep₁.some zk ≪≫ eN₁⟩
  have hx₁ : (G.proj y).1 = 0 := eq_zero_of_poincare_iso_unit hrep₁.some ptsI haddI _ e₁

  have hproj₂ := (hproj y).2
  rw [hy] at hproj₂
  have hsc : schemeHomOverComp zk ν₂ = postComp ν₂ zk := Subtype.ext (schemeHomOverComp_coe _ _)
  obtain ⟨eQ⟩ := hν₂ (𝟙 _) zk
  have e₂ : Nonempty ((hrep₂.some.poincare.pullbackAlong (ptsE (G.proj y).2)).L ≅ SheafOfModules.unit (pullback c₂ (𝟙 _)).ringCatSheaf) := by
    rw [hproj₂, ← hsc]
    exact ⟨isoUnitOfRigidify (rigSection c₂ (𝟙 _) ε₂) (pullback.snd c₂ (𝟙 _)) (pullback.lift_snd _ _ _) eN₂ eQ
      (hrep₂.some.poincare.pullbackAlong _).rigidified.some⟩
  have hx₂ : (G.proj y).2 = 0 := eq_zero_of_poincare_iso_unit hrep₂.some ptsE haddE _ e₂
  exact Prod.ext hx₁ hx₂

end S_ModularCurve_XOneP_exists_pts_comp_fst_eq_and_proj_eq_zero_of_pullback_poincare_pullbackAlong_iso_unit_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_pts_comp_fst_eq_and_proj_eq_zero_of_pullback_poincare_pullbackAlong_iso_unit_twoChartModel_x1_mul (solution)
