-- Prove2me | solution 1 for ModularCurve.XOneP.postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4cf29523-6fa3-5f84-83dd-7c939fb524bc

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
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve"

noncomputable section

namespace P2mProjTransport

theorem nonempty_iso_unit_of_field (k : Type u) [Field k] (M : (Spec (CommRingCat.of k)).Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (M ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  have hpt : ∀ y y' : (Spec (CommRingCat.of k) : Scheme.{u}), y = y' :=
    fun y y' => Subsingleton.elim (α := PrimeSpectrum k) y y'
  let x : (Spec (CommRingCat.of k) : Scheme.{u}) := (default : PrimeSpectrum k)
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.1 x
  have hU : U = ⊤ := by
    refine SetLike.ext fun y => ⟨fun _ => TopologicalSpace.Opens.mem_top y, fun _ => ?_⟩
    rw [hpt y x]
    exact hxU
  subst hU
  exact ⟨((Scheme.Modules.pullbackId _).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.toIso_inv_ι (Spec (CommRingCat.of k))).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
    (Scheme.Modules.pullback _).mapIso eU ≪≫
    Scheme.Modules.pullbackUnitIso _⟩

def rigidifyIsoOfPullbackIsoUnit {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules)
    (e : (Scheme.Modules.pullback σ).obj L ≅ 𝟙_ T.Modules) :
    Scheme.Modules.rigidify σ q L ≅ L :=
  (Iso.refl L ⊗ᵢ ((Scheme.Modules.pullback q).mapIso
      (Scheme.Modules.dualMapIso e ≪≫ MonoidalClosed.unitIsoSelf (𝟙_ T.Modules)) ≪≫
        Scheme.Modules.pullbackUnitIso q)) ≪≫ ρ_ L

section maps

variable {S X T : Scheme.{u}}

def eMap (c : X ⟶ S) (t : T ⟶ S) (σ : S ⟶ S) (ht : t ≫ σ = t) :
    pullback c t ⟶ pullback c (t ≫ σ) :=
  pullback.map c t c (t ≫ σ) (𝟙 X) (𝟙 T) (𝟙 S) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, Category.id_comp, ht])

@[reassoc]
theorem eMap_fst (c : X ⟶ S) (t : T ⟶ S) (σ : S ⟶ S) (ht : t ≫ σ = t) :
    eMap c t σ ht ≫ pullback.fst c (t ≫ σ) = pullback.fst c t :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem eMap_snd (c : X ⟶ S) (t : T ⟶ S) (σ : S ⟶ S) (ht : t ≫ σ = t) :
    eMap c t σ ht ≫ pullback.snd c (t ≫ σ) = pullback.snd c t :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def mMap (c : X ⟶ S) (t : T ⟶ S) (σ σ' : S ⟶ S) (u : X ⟶ X) (hu : u ≫ c = c ≫ σ')
    (hσ : σ ≫ σ' = 𝟙 S) : pullback c (t ≫ σ) ⟶ pullback c t :=
  pullback.map c (t ≫ σ) c t u (𝟙 T) σ' hu.symm
    (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

@[reassoc]
theorem mMap_fst (c : X ⟶ S) (t : T ⟶ S) (σ σ' : S ⟶ S) (u : X ⟶ X) (hu : u ≫ c = c ≫ σ')
    (hσ : σ ≫ σ' = 𝟙 S) :
    mMap c t σ σ' u hu hσ ≫ pullback.fst c t = pullback.fst c (t ≫ σ) ≫ u :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem mMap_snd (c : X ⟶ S) (t : T ⟶ S) (σ σ' : S ⟶ S) (u : X ⟶ X) (hu : u ≫ c = c ≫ σ')
    (hσ : σ ≫ σ' = 𝟙 S) :
    mMap c t σ σ' u hu hσ ≫ pullback.snd c t = pullback.snd c (t ≫ σ) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

def transPt {Dp : Scheme.{u}} {d : Dp ⟶ S} (σ : S ⟶ S) (N : SchemeHomOver (d ≫ σ) d) {t : T ⟶ S}
    (a : SchemeHomOver t d) : SchemeHomOver (t ≫ σ) d :=
  ⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩

@[scoped simp]
theorem transPt_val {Dp : Scheme.{u}} {d : Dp ⟶ S} (σ : S ⟶ S) (N : SchemeHomOver (d ≫ σ) d)
    {t : T ⟶ S} (a : SchemeHomOver t d) : (transPt σ N a).1 = a.1 ≫ N.1 := rfl

end maps

section overR

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {c' : C' ⟶ Spec (CommRingCat.of R)}

@[reassoc]
theorem baseChangeSnd_fst {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem curveChange_fst (f : C' ⟶ C) (hf : f ≫ c = c') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f :=
  pullback.lift_fst _ _ _

def phiPt (D : RelativePic0Designation R c) (k : Type u) [CommRing k] [Algebra R k] :
    SchemeHomOver ((D.baseChange k).toBase ≫ specMap R k) D.toBase :=
  ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩

@[scoped simp]
theorem phiPt_val (D : RelativePic0Designation R c) (k : Type u) [CommRing k] [Algebra R k] :
    (phiPt D k).1 = pullback.fst D.toBase (specMap R k) := rfl

theorem postComp_phiPt_overR_val (D : RelativePic0Designation R c) (k : Type u) [CommRing k] [Algebra R k]
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (b : SchemeHomOver t (D.baseChange k).toBase) :
    (postComp (phiPt D k) (BaseChange.overR k b)).1 = b.1 ≫ pullback.fst D.toBase (specMap R k) := rfl

end overR

theorem engine {R : Type u} [CommRing R] {X : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (k : Type u) [Field k] [Algebra R k]
    {D : RelativePic0Designation R c} (P : RigidifiedLineBundle c ε D.toBase)
    (Pk : RigidifiedLineBundle (baseChange R c k) (sectionBaseChange k ε) (D.baseChange k).toBase)
    (hPk : Nonempty (Pk.L ≅ (BaseChange.ofR c ε k
      (P.pullbackAlong ⟨pullback.fst D.toBase (specMap R k), pullback.condition⟩)).L))
    (σs σs' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (hsinv : σs ≫ σs' = 𝟙 _)
    (hks : specMap R k ≫ σs = specMap R k)
    (u : X ⟶ X) (hu : u ≫ c = c ≫ σs')
    (uk : pullback c (specMap R k) ⟶ pullback c (specMap R k))
    (huk : uk ≫ pullback.fst c (specMap R k) = pullback.fst c (specMap R k) ≫ u)
    (N : SchemeHomOver (D.toBase ≫ σs) D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((P.pullbackAlong (transPt σs N a)).L ≅
        Scheme.Modules.rigidify (rigSection c (t ≫ σs) ε) (pullback.snd c (t ≫ σs))
          ((Scheme.Modules.pullback (mMap c t σs σs' u hu hsinv)).obj (P.pullbackAlong a).L)))
    {Cᵢ : Scheme.{u}} {cᵢ : Cᵢ ⟶ Spec (CommRingCat.of k)} (i : SchemeHomOver cᵢ (baseChange R c k))
    (hi : i.1 ≫ uk = i.1)
    (a a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ha : a'.1 ≫ pullback.fst D.toBase (specMap R k) =
      (a.1 ≫ pullback.fst D.toBase (specMap R k)) ≫ N.1) :
    Nonempty ((Scheme.Modules.pullback (curveChange i.1 i.2 (𝟙 _))).obj (Pk.pullbackAlong a').L ≅
      (Scheme.Modules.pullback (curveChange i.1 i.2 (𝟙 _))).obj (Pk.pullbackAlong a).L) := by

  have isoA : ∀ b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase,
      Nonempty ((Pk.pullbackAlong b).L ≅
        (Scheme.Modules.pullback (BaseChange.κ c k (𝟙 (Spec (CommRingCat.of k)))).hom).obj
          (P.pullbackAlong (postComp (phiPt D k) (BaseChange.overR k b))).L) := fun b =>
    ⟨(Scheme.Modules.pullback (baseChangeSnd (baseChange R c k) b)).mapIso hPk.some ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (BaseChange.baseChangeSnd_κ_hom c k b)).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso
        ((Scheme.Modules.pullbackComp _ _).app P.L ≪≫
          (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c (phiPt D k) (BaseChange.overR k b))).app P.L)⟩

  have ht₀ : (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ σs = 𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k := by
    rw [Category.assoc, hks]

  obtain ⟨eN⟩ := hN (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) (postComp (phiPt D k) (BaseChange.overR k a))
  have he : eMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs ht₀ ≫
      baseChangeSnd c (transPt σs N (postComp (phiPt D k) (BaseChange.overR k a))) =
        baseChangeSnd c (postComp (phiPt D k) (BaseChange.overR k a')) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeSnd_fst, eMap_fst]
    · simp only [Category.assoc, baseChangeSnd_snd, eMap_snd_assoc, transPt_val, postComp_phiPt_overR_val, ha]

  have hQinv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (rigSection c ((𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) ≫ σs) ε)).obj
        ((Scheme.Modules.pullback (mMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs σs' u hu hsinv)).obj
          (P.pullbackAlong (postComp (phiPt D k) (BaseChange.overR k a))).L)) :=
    ((P.pullbackAlong _).isInvertible.pullback _).pullback _
  obtain ⟨eu⟩ := nonempty_iso_unit_of_field k _ hQinv
  let iB : (P.pullbackAlong (postComp (phiPt D k) (BaseChange.overR k a'))).L ≅
      (Scheme.Modules.pullback ((eMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs ht₀ ≫
          mMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs σs' u hu hsinv) ≫
            baseChangeSnd c (postComp (phiPt D k) (BaseChange.overR k a)))).obj P.L :=
    (Scheme.Modules.pullbackCongr he.symm).app P.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app P.L).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (eN ≪≫ rigidifyIsoOfPullbackIsoUnit _ _ _ eu) ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackComp _ _).app P.L

  have key : curveChange i.1 i.2 (𝟙 _) ≫ (BaseChange.κ c k (𝟙 (Spec (CommRingCat.of k)))).hom ≫
      eMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs ht₀ ≫
        mMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs σs' u hu hsinv =
      curveChange i.1 i.2 (𝟙 _) ≫ (BaseChange.κ c k (𝟙 (Spec (CommRingCat.of k)))).hom := by
    have hκ := BaseChange.κ_hom_fst c k (𝟙 (Spec (CommRingCat.of k)))
    apply pullback.hom_ext
    · simp only [Category.assoc, mMap_fst, eMap_fst_assoc]
      rw [reassoc_of% hκ, hκ, curveChange_fst_assoc, curveChange_fst_assoc, ← huk, reassoc_of% hi]
    · simp only [Category.assoc, mMap_snd, eMap_snd]
  have key' : (curveChange i.1 i.2 (𝟙 _) ≫ (BaseChange.κ c k (𝟙 (Spec (CommRingCat.of k)))).hom) ≫
      ((eMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs ht₀ ≫
          mMap c (𝟙 (Spec (CommRingCat.of k)) ≫ specMap R k) σs σs' u hu hsinv) ≫
            baseChangeSnd c (postComp (phiPt D k) (BaseChange.overR k a))) =
      (curveChange i.1 i.2 (𝟙 _) ≫ (BaseChange.κ c k (𝟙 (Spec (CommRingCat.of k)))).hom) ≫
        baseChangeSnd c (postComp (phiPt D k) (BaseChange.overR k a)) := by
    simp only [Category.assoc]
    rw [reassoc_of% key]
  obtain ⟨iA⟩ := isoA a
  obtain ⟨iA'⟩ := isoA a'
  exact ⟨(Scheme.Modules.pullback _).mapIso (iA' ≪≫ (Scheme.Modules.pullback _).mapIso iB) ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app P.L ≪≫
    (Scheme.Modules.pullbackCongr key').app P.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app P.L).symm ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso iA.symm⟩

end P2mProjTransport
p2m_reactivate "P2MW.S_ModularCurve_XOneP_postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul.P2mProjTransport"

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul.P2mProjTransport"

open AlgebraicCurve in

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

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (hsk : ∀ (s' : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s' • a) = algebraMap A k a)
    (s : L ≃ₐ[ℚ] L)
    (u : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hu : u ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))))
    (uk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (huk₁ : uk.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ u)
    (huk₂ : uk.hom ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))

    (hsinv : (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) = 𝟙 (Spec (CommRingCat.of A)))

    (N : SchemeHomOver (D.toBase ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) D.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hrep.some.poincare.pullbackAlong
          (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) D.toBase)).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))))
          ((Scheme.Modules.pullback
              (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) (ModularCurve.TwoChart.modelTo A (↥K) j) t u (𝟙 T) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))
                hu.symm (by rw [Category.assoc, hsinv, Category.comp_id, Category.id_comp]))).obj
            (hrep.some.poincare.pullbackAlong a).L)))
    :
    ∀ (a a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase),
      a'.1 ≫ pullback.fst D.toBase (specMap A k) = (a.1 ≫ pullback.fst D.toBase (specMap A k)) ≫ N.1 →
      (i₁.1 ≫ uk.hom = i₁.1 →
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) a' =
          postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) a) ∧
      (i₂.1 ≫ uk.hom = i₂.1 → postComp ν₂ a' = postComp ν₂ a) := by
  intro a a' ha

  have hks : specMap A k ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) =
      specMap A k := by
    have hring : (algebraMap A k).comp (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s) = algebraMap A k :=
      RingHom.ext fun x => hsk s x
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  refine ⟨fun h₁ => ?_, fun h₂ => ?_⟩
  ·
    refine hrep₁.some.ext_of_iso (𝟙 _) _ _ ⟨?_⟩
    have j : ∀ b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase,
        (hrep₁.some.poincare.pullbackAlong
            (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) b)).L ≅
          (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 (𝟙 _))).obj (hreps.poincare.pullbackAlong b).L :=
      fun b =>
        (hrep₁.some.poincare.pullbackAlongPullbackAlongIso' _ b).symm ≪≫
          (Scheme.Modules.pullback _).mapIso (hrep₁.some.classify_spec (D.baseChange k).toBase
            (hreps.poincare.pullbackCurve i₁.1 i₁.2 hε₁)
            (FibrewiseAlgEquivZero.pullbackCurve i₁.1 i₁.2 hε₁ hreps.poincare_mem)).some ≪≫
          hreps.poincare.pullbackCurvePullbackAlongIso i₁.1 i₁.2 hε₁ b
    exact j a' ≪≫
      (P2mProjTransport.engine k hrep.some.poincare hreps.poincare hPk _ _ hsinv hks u hu uk.hom huk₁ N hN
        i₁ h₁ a a' ha).some ≪≫ (j a).symm
  ·
    refine hrep₂.some.ext_of_iso (𝟙 _) _ _ ⟨?_⟩
    exact (hν₂ (𝟙 _) a').some ≪≫
      Scheme.Modules.rigidifyMapIso _ _
        (P2mProjTransport.engine k hrep.some.poincare hreps.poincare hPk _ _ hsinv hks u hu uk.hom huk₁ N hN
          i₂ h₂ a a' ha).some ≪≫
      (hν₂ (𝟙 _) a).some.symm

end S_ModularCurve_XOneP_postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_postComp_pullbackHom_eq_and_postComp_eq_of_comp_fst_eq_comp_galoisTransport_of_comp_fibreIso_eq_twoChartModel_x1_mul (solution)
