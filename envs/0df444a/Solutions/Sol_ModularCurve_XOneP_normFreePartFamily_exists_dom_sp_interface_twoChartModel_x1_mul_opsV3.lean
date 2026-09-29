-- Prove2me | solution 1 for ModularCurve.XOneP.normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/528de181-f45c-5b07-a78b-2e002996a4b8

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
import Definitions.Def_ModularCurve_JOnePOpsV3
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
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinned
import Definitions.Def_ModularCurve_QExpSemistableSpecializationPinnedV3
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace FamAux

theorem exists_normal_core {G : Type*} [Group G] (P H : Subgroup G) (hH : H ≤ P)
    [(H.subgroupOf P).FiniteIndex] :
    ∃ N ≤ H, (N.subgroupOf P).FiniteIndex ∧ ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
  classical
  refine ⟨((H.subgroupOf P).normalCore).map P.subtype, ?_, ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' : y ∈ H.subgroupOf P := Subgroup.normalCore_le _ hy
    simpa [Subgroup.mem_subgroupOf] using hy'
  ·
    have h : (((H.subgroupOf P).normalCore).map P.subtype).subgroupOf P = (H.subgroupOf P).normalCore := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    rw [h]
    infer_instance
  ·
    intro g hg n hn
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, by simp⟩
    exact (inferInstance : ((H.subgroupOf P).normalCore).Normal).conj_mem y hy ⟨g, hg⟩

theorem exists_common_level {G : Type*} [Group G] (P I I' : Subgroup G) (hI : I ≤ P) (hI' : I' ≤ P)
    [(I.subgroupOf P).FiniteIndex] [(I'.subgroupOf P).FiniteIndex] :
    ∃ N : Subgroup G, N ≤ I ∧ N ≤ I' ∧ (N.subgroupOf P).FiniteIndex ∧ ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
  haveI : ((I ⊓ I').subgroupOf P).FiniteIndex := by
    have h : (I ⊓ I').subgroupOf P = I.subgroupOf P ⊓ I'.subgroupOf P := by
      ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [h]
    infer_instance
  obtain ⟨N, hN, hfi, hnorm⟩ := exists_normal_core P (I ⊓ I') (inf_le_left.trans hI)
  exact ⟨N, hN.trans inf_le_left, hN.trans inf_le_right, hfi, hnorm⟩

end FamAux

open scoped Pointwise

namespace FamAux

section Cyclotomic

variable (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
  (ζ : L) (hζ : IsPrimitiveRoot ζ p) [Algebra L (AlgebraicClosure ℚ)]

include p in

theorem restrict_gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ s : L ≃ₐ[ℚ] L, ∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l) := by
  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional ({p} : Set ℕ) ℚ L
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois ({p} : Set ℕ) ℚ L
  exact ⟨σ.restrictNormal L, fun l => (AlgEquiv.restrictNormal_commutes σ L l).symm⟩

omit [Algebra L (AlgebraicClosure ℚ)] in
include hζ in

theorem gal_eq_one_of_apply_zeta (s : L ≃ₐ[ℚ] L) (hs : s ζ = ζ) : s = 1 := by
  haveI : NeZero (p : L) := NeZero.charZero
  apply AlgEquiv.coe_algHom_injective
  refine (hζ.powerBasis ℚ).algHom_ext ?_
  simpa [IsPrimitiveRoot.powerBasis_gen] using hs

omit [IsCyclotomicExtension {p} ℚ L] in
include hζ in

theorem pow_of_forall_rootsOfUnity (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L)
    (hs : ∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l))
    (u : ℕ) (hu : ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ' ^ u) :
    s ζ = ζ ^ u ∧ ¬ p ∣ u := by
  have hinj : Function.Injective (algebraMap L (AlgebraicClosure ℚ)) := (algebraMap L (AlgebraicClosure ℚ)).injective
  have hζp : (algebraMap L (AlgebraicClosure ℚ) ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have key : algebraMap L (AlgebraicClosure ℚ) (s ζ) = algebraMap L (AlgebraicClosure ℚ) (ζ ^ u) := by
    rw [← hs, hu _ hζp, map_pow]
  refine ⟨hinj key, fun hpu => ?_⟩

  have h1 : s ζ = 1 := by
    rw [hinj key]; obtain ⟨c, rfl⟩ := hpu; rw [pow_mul, hζ.pow_eq_one, one_pow]
  have hζ1 : ζ = 1 := by
    have := congrArg s.symm h1
    simpa using this
  exact hζ.ne_one (Fact.out : p.Prime).one_lt hζ1

end Cyclotomic

section Places

variable (Pl : ValuationSubring (AlgebraicClosure ℚ))

theorem mem_of_mem_decompositionSubgroup (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ Pl.decompositionSubgroup ℚ) (x : AlgebraicClosure ℚ) (hx : x ∈ Pl) : σ x ∈ Pl := by
  have h : σ • Pl = Pl := hσ
  have : σ • x ∈ σ • Pl := ValuationSubring.smul_mem_pointwise_smul σ x Pl hx
  rw [h] at this
  exact this

theorem inertiaSubgroupIn_le_decompositionSubgroup :
    Pl.inertiaSubgroupIn ℚ ≤ Pl.decompositionSubgroup ℚ := by
  rintro σ ⟨d, -, rfl⟩
  exact d.2

theorem residue_eq_of_mem_inertiaSubgroupIn (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ Pl.inertiaSubgroupIn ℚ) (x : AlgebraicClosure ℚ) (hx : x ∈ Pl) (hσx : σ x ∈ Pl) :
    IsLocalRing.residue ↥Pl ⟨σ x, hσx⟩ = IsLocalRing.residue ↥Pl ⟨x, hx⟩ := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  have hker : MulSemiringAction.toRingAut (Pl.decompositionSubgroup ℚ) (IsLocalRing.ResidueField ↥Pl) d = 1 := hd
  have h1 : d • IsLocalRing.residue ↥Pl ⟨x, hx⟩ = IsLocalRing.residue ↥Pl ⟨x, hx⟩ := by
    have := DFunLike.congr_fun hker (IsLocalRing.residue ↥Pl ⟨x, hx⟩)
    simpa [MulSemiringAction.toRingAut_apply] using this
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  convert h1 using 2
  rfl

end Places

end FamAux

open ModularCurve IntermediateField in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in
theorem solution
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)] [CharP (IsLocalRing.ResidueField ↥Pl) p] [Algebra A (IsLocalRing.ResidueField ↥Pl)]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))) (c₂ : C₂ ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl))) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)) (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) (IsLocalRing.ResidueField ↥Pl)) (sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε)) (D.baseChange (IsLocalRing.ResidueField ↥Pl)))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε (IsLocalRing.ResidueField ↥Pl)
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation (IsLocalRing.ResidueField ↥Pl) c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation (IsLocalRing.ResidueField ↥Pl) c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))) (a : SchemeHomOver t (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
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
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) D₂.toBase)
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
    (O : ModularCurve.JOneP.NeronSpecialFibreOpsV3 G)
    (hO :
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (y : G.J0s),
        (pts (O.hecke ℓ y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)).1) ∧
      (∀ (b : (ZMod p)ˣ) (d : ℕ), d.Coprime (M * p) → (d : ZMod M) = 1 → (d : ZMod p) = (b : ZMod p) →
        ∀ y : G.J0s,
          (pts (O.diamondP b y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
            ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.diamondGen d)).1) ∧
      (∀ d : ℕ, d.Coprime (M * p) → (d : ZMod p) = 1 → ∀ y : G.J0s,
        (pts (O.diamondN d y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (φ (ModularCurve.diamondGen d)).1) ∧

      (∀ (b : (ZMod p)ˣ) (s : L ≃ₐ[ℚ] L), s ζ = ζ ^ (b : ZMod p).val → ∀ y : G.J0s,
        (pts (O.inertia b y)).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) =
          ((pts y).1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ (τ s).1) )
    (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (hAlgκ : algebraMap A (IsLocalRing.ResidueField ↥Pl) = (IsLocalRing.residue ↥Pl).comp ρ)
    (hF3 : ∀
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
    (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
    (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),

    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    ∃ (ρI : A →+* ↥OI) (hρI : OI.subtype.comp ρI = algebraMap A (AlgebraicClosure ℚ)),

      let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)

      let DOI := SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase
      let Dκ := SchemeHomOver (Spec.map (CommRingCat.ofHom (toκ.comp ρI))) D.toBase

      let dom : Set (ModularCurve.JOne (M * p)) :=
        {x | ∃ z : DOI, (gpts x).1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1}

      (∀ x ∈ dom, ∀ σ ∈ I, σ • x = x) ∧

      (∀ z z' : DOI, Spec.map (CommRingCat.ofHom OI.subtype) ≫ z.1 = Spec.map (CommRingCat.ofHom OI.subtype) ≫ z'.1 → z = z') ∧

      (0 ∈ dom ∧ ∀ x ∈ dom, ∀ y ∈ dom, x - y ∈ dom) ∧

      (letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom ρI))
       letI := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup
          (Spec.map (CommRingCat.ofHom (toκ.comp ρI)))
       ∀ n : ℕ, 0 < n → ¬ p ∣ n →
         (∀ z : DOI, z ^ n = 1 → Spec.map (CommRingCat.ofHom toκ) ≫ z.1 = (1 : Dκ).1 → z = 1) ∧
         (∀ w : Dκ, w ^ n = 1 → ∃ z : DOI, z ^ n = 1 ∧ w.1 = Spec.map (CommRingCat.ofHom toκ) ≫ z.1)) ∧

      (∀ φ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Pl.IsFrobeniusAt φ' p →
        (∀ σ, σ ∈ I ↔ φ' * σ * φ'⁻¹ ∈ I) → ∀ x ∈ dom, φ' • x ∈ dom))
    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)
    (h𝒜 :

      IsClosedImmersion ι.1 ∧

      IsProper a ∧ Smooth a ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s)) ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι))) ∧

      (∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1) ∧

      (∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)))
    (hF10 :
    ∀ (T' : Type) [CommRing T'] [Algebra (IsLocalRing.ResidueField ↥Pl) T']
      (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T'))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
      (∃ z : Spec (CommRingCat.of T') ⟶ 𝒜,
          z ≫ a = Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T')) ≫ specMap A (IsLocalRing.ResidueField ↥Pl) ∧
          v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = z ≫ ι.1) →
      (v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫
          (φ (∑ b : (ZMod p)ˣ, ModularCurve.diamondGen
            ((ZMod.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpM)).symm ((b : ZMod p), 1)).val)).1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one
          (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ↥Pl) T')) ≫ specMap A (IsLocalRing.ResidueField ↥Pl))).1)

    (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField ↥Pl) M)
    (Mdl₁ : AlgebraicCurve.CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A (IsLocalRing.ResidueField ↥Pl)) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (IsLocalRing.ResidueField ↥Pl))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥Pl) (x.map (algebraMap A (IsLocalRing.ResidueField ↥Pl))) / HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥Pl) (y.map (algebraMap A (IsLocalRing.ResidueField ↥Pl))))

    (hεC₂ : ∀ t, ((sectionBaseChange (IsLocalRing.ResidueField ↥Pl) ε).1).base t ∉ Set.range i₂.1.base)
    (hεgal : ∀ (s : L ≃ₐ[ℚ] L) (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j),
      ws ≫ ModularCurve.TwoChart.modelTo A (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) →
      ∀ (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L)) →
      ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ε.1 ≫ ws = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1)
    (hPTS :
    (∀ a b : G.J0s, pts (a + b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul _ (pts a) (pts b)) ∧
    pts 0 = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).one _)
    (nodesIg : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)))
    (Ψ : G.J0s ≃+ AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg)
    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (θ₂ : G.JE ≃+ AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (hF4c :

      (∀ σ : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w),
        σ ∈ nodesIg ↔ ∃ (z : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ pullback i₁.1 i₂.1)
          (hz₁ : (z ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : (z ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _),
          σ.1 = Mdl₁.pointEquivPlace ⟨(z ≫ pullback.fst i₁.1 i₂.1) ≫ e₁.inv,
            by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact hz₁⟩ ∧
          σ.2 = Mdl₂.pointEquivPlace ⟨(z ≫ pullback.snd i₁.1 i₂.1) ≫ e₂.inv,
            by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact hz₂⟩) ∧
      nodesIg.card = n ∧
      Set.InjOn Prod.fst (nodesIg : Set (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))) ∧
      Set.InjOn Prod.snd (nodesIg : Set (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) × AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))) ∧

      (∀ x : G.J0s, AlgebraicCurve.GluedPic0.toPic0Pair nodesIg (Ψ x) = (θ₁ (G.proj x).1, θ₂ (G.proj x).2)) ∧

      (G.torus.map Ψ.toAddMonoidHom = (AlgebraicCurve.GluedPic0.nodeUnit nodesIg).range) ∧

      (∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₁),
        Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
          (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
        ∃ Dv : Divisor.degZero (K := (IsLocalRing.ResidueField ↥Pl)) (F := ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)),
          (Dv : Divisor (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) =
            Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
              Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
          θ₁ g = Pic0.mk Dv) ∧

      (∀ (g : G.JE) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) c₂),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (ptsE g)).L ≅
          (RelEffCartierDiv.ofPoint c₂ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₂ ε₂.1 ε₂.2).idealModule) →
        ∃ Dv : Divisor.degZero (K := (IsLocalRing.ResidueField ↥Pl)) (F := ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)),
          (Dv : Divisor (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) =
            Finsupp.single (Mdl₂.pointEquivPlace ⟨x.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact x.2⟩) 1 -
              Finsupp.single (Mdl₂.pointEquivPlace ⟨ε₂.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact ε₂.2⟩) 1 ∧
          θ₂ g = Pic0.mk Dv))
    (frobT : SemilinearAut (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w))
    (hfrobT : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) (n : ℤ),
      ((frobT • x : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)).coeff n = ((x : LaurentSeries (IsLocalRing.ResidueField ↥Pl)).coeff n) ^ p)
    :
    ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),
    ∃ (dom : AddSubgroup (ModularCurve.JOne (M * p)))
      (sp : ↥dom →+ AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg),
      ((∀ y : ModularCurve.JOne (M * p), y ∈ dom ↔ ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase,
          (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1) ∧
      (∀ (y : ModularCurve.JOne (M * p)) (hy : y ∈ dom) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase)
        (hz : (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1) (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase),
        u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring)))) ≫ z.1 →
        sp ⟨y, hy⟩ = Ψ (pts.symm u))) ∧

      (∀ y ∈ dom, ∀ σ ∈ I, σ • y = y) ∧

      (∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          Pl.IsFrobeniusAt φ p → (∀ σ, σ ∈ I ↔ φ * σ * φ⁻¹ ∈ I) → ∀ y ∈ dom, φ • y ∈ dom) ∧

      (∀ y : dom,
          (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧
            n • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField (M * p)))) = 0) →
            sp y = 0 → y = 0) ∧

      (∀ ξ : GluedPic0 (IsLocalRing.ResidueField ↥Pl) (ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • ξ = 0) →
          ∃ y : dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧
            n • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField (M * p)))) = 0) ∧ sp y = ξ) := by
  classical
  have hnodes := hF4c.1
  have hcard := hF4c.2.1
  have hinj₁ := hF4c.2.2.1
  have hinj₂ := hF4c.2.2.2.1
  have hsquare := hF4c.2.2.2.2.1
  have htorus := hF4c.2.2.2.2.2.1
  have hθpin₁ := hF4c.2.2.2.2.2.2.1
  have hθpin₂ := hF4c.2.2.2.2.2.2.2
  have hcompρ : ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
      (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex),
      ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left :
          Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring ≤ Pl.toSubring))).comp
        (Classical.choose (hF3 I hI hIμ hIf)) = algebraMap A (IsLocalRing.ResidueField ↥Pl) := by
    intro I hI hIμ hIf
    have hρI := (Classical.choose_spec (hF3 I hI hIμ hIf)).fst
    have hincl : (Subring.inclusion (inf_le_left :
        Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring ≤ Pl.toSubring)).comp
          (Classical.choose (hF3 I hI hIμ hIf)) = ρ := by
      apply RingHom.ext; intro a'; apply Subtype.ext
      have h1 := congrArg (fun f : A →+* AlgebraicClosure ℚ => f a') hρI
      have h2 := congrArg (fun f : A →+* AlgebraicClosure ℚ => f a') hρ
      exact h1.trans h2.symm
    rw [RingHom.comp_assoc, hincl, hAlgκ]

  let redκ : ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
      (hIf : (I.subgroupOf (Pl.inertiaSubgroupIn ℚ)).FiniteIndex)
      (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase),
      SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase :=
    fun I hI hIμ hIf z =>
      ⟨pullback.lift
          (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left :
              Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring ≤ Pl.toSubring)))) ≫ z.1)
          (𝟙 _)
          (by

            simp only [Category.id_comp, Category.assoc, z.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcompρ I hI hIμ hIf]),
        pullback.lift_snd _ _ _⟩
  intro I hI hIμ hIf
  have hρI := (Classical.choose_spec (hF3 I hI hIμ hIf)).fst
  have h := (Classical.choose_spec (hF3 I hI hIμ hIf)).snd

  have hS : Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf))) = specMap A (AlgebraicClosure ℚ) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρI]
  have hTA : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring)))) ≫ Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf))) =
      Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf)))) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hb : 𝟙 _ ≫ specMap A (IsLocalRing.ResidueField ↥Pl) =
      Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf)))) := by
    simp only [Category.id_comp, hcompρ I hI hIμ hIf]
  have hT1 : 𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl))) ≫ (𝟙 _ ≫ specMap A (IsLocalRing.ResidueField ↥Pl)) =
      Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf)))) := by
    simp only [Category.id_comp]; exact hb
  letI iQ : Group (SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase) := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup _
  letI iOI : Group (SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase) := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup _
  letI iκA : Group (SchemeHomOver (Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf))))) D.toBase) := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).pointGroup _
  letI iS : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase) := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).pointGroup _

  let gH : Multiplicative (ModularCurve.JOne (M * p)) →* SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase :=
    MonoidHom.mk' (fun u => gpts (Multiplicative.toAdd u)) (fun u v => hgadd _ _)
  let pH : Multiplicative G.J0s →* SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase :=
    MonoidHom.mk' (fun u => pts (Multiplicative.toAdd u)) (fun u v => hPTS.1 _ _)
  let cS : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase →* SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase :=
    MonoidHom.mk' (fun z => GoodReductionJacobian.schemeHomOverComp _ hS z) (fun u v => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul_natural _ _ _ hS u v)
  let cT : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase →* SchemeHomOver (Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf))))) D.toBase :=
    MonoidHom.mk' (fun z => GoodReductionJacobian.schemeHomOverComp _ hTA z) (fun u v => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul_natural _ _ _ hTA u v)
  have PΘ : ∀ u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase,
      (u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl))) ≫ D.toBase = 𝟙 _ ≫ specMap A (IsLocalRing.ResidueField ↥Pl) := fun u => by
    have hu : u.1 ≫ pullback.snd D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = 𝟙 _ := u.2
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]
  let Θ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase →* SchemeHomOver (Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf))))) D.toBase :=
    MonoidHom.mk' (fun u => ⟨u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), (PΘ u).trans hb⟩)
      (by
        intro u v
        have hc := AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat A
          (ModularCurve.TwoChart.modelTo A (↥K) j) ε D hrep.some (IsLocalRing.ResidueField ↥Pl) hreps hPk (𝟙 _) u v
          ⟨u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), PΘ u⟩ ⟨v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), PΘ v⟩ rfl rfl
        have hn := congrArg Subtype.val ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul_natural _ _ (𝟙 _) hT1
          ⟨u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), PΘ u⟩ ⟨v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), PΘ v⟩)
        have e1 : GoodReductionJacobian.schemeHomOverComp (𝟙 _) hT1 ⟨u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), PΘ u⟩ =
            (⟨u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), (PΘ u).trans hb⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf))))) D.toBase) := Subtype.ext (Category.id_comp _)
        have e2 : GoodReductionJacobian.schemeHomOverComp (𝟙 _) hT1 ⟨v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), PΘ v⟩ =
            (⟨v.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)), (PΘ v).trans hb⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf))))) D.toBase) := Subtype.ext (Category.id_comp _)
        apply Subtype.ext
        exact hc.trans (((GoodReductionJacobian.schemeHomOverComp_coe _ _ _).symm.trans hn).trans
          (congrArg Subtype.val (congrArg₂ (fun a' b' => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ a' b') e1 e2))))
  have hgH : ∀ u : ModularCurve.JOne (M * p), gH (Multiplicative.ofAdd u) = gpts u := fun _ => rfl
  have hpH : ∀ u : G.J0s, pH (Multiplicative.ofAdd u) = pts u := fun _ => rfl
  have hcS : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase, (cS z).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1 := fun _ => rfl
  have hcT : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase, (cT z).1 = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring)))) ≫ z.1 := fun _ => rfl
  have hΘ : ∀ u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase, (Θ u).1 = u.1 ≫ pullback.fst D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) := fun _ => rfl

  have hcS_inj : ∀ z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase, cS z = cS z' → z = z' :=
    fun z z' e => h.2.1 z z' (congrArg Subtype.val e)
  have hΘred : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase, Θ (redκ I hI hIμ hIf z) = cT z :=
    fun z => Subtype.ext (pullback.lift_fst _ _ _)
  have hredΘ : ∀ (u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)))) (D.baseChange (IsLocalRing.ResidueField ↥Pl)).toBase)
      (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase), (Θ u).1 = (cT z).1 → redκ I hI hIμ hIf z = u := fun u z e => by
    have hu : u.1 ≫ pullback.snd D.toBase (specMap A (IsLocalRing.ResidueField ↥Pl)) = 𝟙 _ := u.2
    exact Subtype.ext (pullback.hom_ext ((pullback.lift_fst _ _ _).trans e.symm) ((pullback.lift_snd _ _ _).trans hu.symm))

  have hgpow : ∀ (k : ℕ) (u : ModularCurve.JOne (M * p)), gpts (k • u) = (gpts u) ^ k := fun k u => by
    rw [← hgH, ← hgH, ofAdd_nsmul, map_pow]
  have hg0 : gpts 0 = 1 := (hgH 0).symm.trans (map_one gH)
  have hppow : ∀ (k : ℕ) (u : G.J0s), pts (k • u) = (pts u) ^ k := fun k u => by
    rw [← hpH, ← hpH, ofAdd_nsmul, map_pow]
  have hp0 : pts 0 = 1 := (hpH 0).symm.trans (map_one pH)

  let domI : AddSubgroup (ModularCurve.JOne (M * p)) :=
    { carrier := {x | ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase,
        (gpts x).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1}
      add_mem' := by
        intro a' b' ha hb
        have hsub := h.2.2.1
        have h0 : _ := hsub.1
        have hnb := hsub.2 _ h0 _ hb
        have hab := hsub.2 _ ha _ hnb
        simpa [zero_sub, sub_neg_eq_add] using hab
      zero_mem' := h.2.2.1.1
      neg_mem' := by
        intro a' ha
        simpa [zero_sub] using h.2.2.1.2 _ h.2.2.1.1 _ ha }
  let spF : ↥domI → AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField ↥Pl) M w) nodesIg :=
    fun x => Ψ (pts.symm (redκ I hI hIμ hIf (Classical.choose x.2)))
  have hspI : ∀ (y : ModularCurve.JOne (M * p))
      (hy : ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase, (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1)
      (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase) (hz : (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1),
      spF ⟨y, hy⟩ = Ψ (pts.symm (redκ I hI hIμ hIf z)) := fun y hy z hz =>
    congrArg (fun z0 => Ψ (pts.symm (redκ I hI hIμ hIf z0))) (h.2.1 _ _ ((Classical.choose_spec hy).symm.trans hz))
  refine ⟨domI, AddMonoidHom.mk' spF ?_, ⟨fun y => Iff.rfl, fun y hy z hz u hu =>
    (hspI y hy z hz).trans (congrArg (fun w0 => Ψ (pts.symm w0)) (hredΘ u z hu))⟩, h.1, h.2.2.2.2, ?_, ?_⟩
  ·

    intro x y
    have huniq := (Classical.choose_spec (hF3 I hI hIμ hIf)).snd.2.1
    have hρI' := (Classical.choose_spec (hF3 I hI hIμ hIf)).fst

    have hS : Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫
        Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf))) = specMap A (AlgebraicClosure ℚ) := by
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρI']

    have hT : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left :
        Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring ≤ Pl.toSubring)))) ≫
        Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf))) =
        𝟙 _ ≫ specMap A (IsLocalRing.ResidueField ↥Pl) := by
      simp only [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcompρ I hI hIμ hIf]

    have hx := Classical.choose_spec x.2
    have hy := Classical.choose_spec y.2
    have hxy := Classical.choose_spec (x + y).2
    have ex : GoodReductionJacobian.schemeHomOverComp _ hS (Classical.choose x.2) =
        gpts (x : ModularCurve.JOne (M * p)) := Subtype.ext hx.symm
    have ey : GoodReductionJacobian.schemeHomOverComp _ hS (Classical.choose y.2) =
        gpts (y : ModularCurve.JOne (M * p)) := Subtype.ext hy.symm

    have emul : Classical.choose (x + y).2 =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _
          (Classical.choose x.2) (Classical.choose y.2) := by
      refine huniq _ _ (hxy.symm.trans ?_)
      have hnat := congrArg Subtype.val
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul_natural
          _ _ _ hS (Classical.choose x.2) (Classical.choose y.2))
      have e2 : (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _
            (GoodReductionJacobian.schemeHomOverComp _ hS (Classical.choose x.2))
            (GoodReductionJacobian.schemeHomOverComp _ hS (Classical.choose y.2)) =
          gpts ((x : ModularCurve.JOne (M * p)) + (y : ModularCurve.JOne (M * p))) :=
        (congrArg₂ (fun u v => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ u v) ex ey).trans
          (hgadd (x : ModularCurve.JOne (M * p)) (y : ModularCurve.JOne (M * p))).symm
      exact ((congrArg Subtype.val e2).symm.trans hnat.symm)

    have key : redκ I hI hIμ hIf ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _
          (Classical.choose x.2) (Classical.choose y.2)) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul _
          (redκ I hI hIμ hIf (Classical.choose x.2)) (redκ I hI hIμ hIf (Classical.choose y.2)) := by
      have hnat := congrArg Subtype.val
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul_natural
          _ _ _ hT (Classical.choose x.2) (Classical.choose y.2))
      have hcompat := AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat A
        (ModularCurve.TwoChart.modelTo A (↥K) j) ε D hrep.some (IsLocalRing.ResidueField ↥Pl) hreps hPk (𝟙 _)
        (redκ I hI hIμ hIf (Classical.choose x.2)) (redκ I hI hIμ hIf (Classical.choose y.2))
        (GoodReductionJacobian.schemeHomOverComp _ hT (Classical.choose x.2))
        (GoodReductionJacobian.schemeHomOverComp _ hT (Classical.choose y.2))
        (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm
      refine Subtype.ext (pullback.hom_ext ?_ ?_)
      · refine Eq.trans ?_ (hnat.trans hcompat.symm)
        exact pullback.lift_fst _ _ _
      · exact (pullback.lift_snd _ _ _).trans
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul _ _ _).2.symm

    have hadd' : pts.symm ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul _
          (redκ I hI hIμ hIf (Classical.choose x.2)) (redκ I hI hIμ hIf (Classical.choose y.2))) =
        pts.symm (redκ I hI hIμ hIf (Classical.choose x.2)) + pts.symm (redκ I hI hIμ hIf (Classical.choose y.2)) :=
      (Equiv.symm_apply_eq pts).2
        ((hPTS.1 _ _).trans
          (congrArg₂ (fun u v => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul _ u v)
            (Equiv.apply_symm_apply pts _) (Equiv.apply_symm_apply pts _))).symm
    calc Ψ (pts.symm (redκ I hI hIμ hIf (Classical.choose (x + y).2)))
        = Ψ (pts.symm (redκ I hI hIμ hIf ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _
            (Classical.choose x.2) (Classical.choose y.2)))) :=
          congrArg (fun z0 => Ψ (pts.symm (redκ I hI hIμ hIf z0))) emul
      _ = Ψ (pts.symm (redκ I hI hIμ hIf (Classical.choose x.2)) + pts.symm (redκ I hI hIμ hIf (Classical.choose y.2))) :=
          congrArg Ψ ((congrArg pts.symm key).trans hadd')
      _ = _ := map_add Ψ _ _
  ·
    intro yd hyn hsp0
    have Hob1 := hyn
    choose n hn0 hpn hny using Hob1
    have Hob2 := (show ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (Classical.choose (hF3 I hI hIμ hIf)))) D.toBase,
      (gpts (yd : ModularCurve.JOne (M * p))).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1 from yd.2)
    choose z hz using Hob2

    have h0 : Ψ (pts.symm (redκ I hI hIμ hIf z)) = 0 := (hspI yd.1 yd.2 z hz).symm.trans hsp0
    have h1 : redκ I hI hIμ hIf z = 1 :=
      ((Equiv.symm_apply_eq pts).1 ((map_eq_zero_iff Ψ Ψ.injective).1 h0)).trans hp0

    have h2 : cS z = gpts (yd : ModularCurve.JOne (M * p)) := Subtype.ext hz.symm
    have h3 : z ^ n = 1 := hcS_inj _ _ (by
      simp only [map_pow, map_one, h2, ← hgpow, hny, hg0])

    have h4 : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring)))) ≫ z.1 = (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom (((IsLocalRing.residue ↥Pl).comp (Subring.inclusion (inf_le_left : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring) ≤ Pl.toSubring))).comp (Classical.choose (hF3 I hI hIμ hIf))))) D.toBase).1 :=
      ((hcT z).symm.trans (congrArg Subtype.val ((hΘred z).symm.trans ((congrArg Θ h1).trans (map_one Θ)))))

    have h5 : z = 1 := (h.2.2.2.1 n hn0 hpn).1 z h3 h4
    have h6 : gpts (yd : ModularCurve.JOne (M * p)) = gpts 0 := by
      simp only [← h2, h5, map_one, hg0]
    exact Subtype.ext (gpts.injective h6)
  ·
    intro ξ hξ
    have Hob3 := hξ
    choose n hn0 hpn hnξ using Hob3

    have hu0 : pts (Ψ.symm ξ) ^ n = 1 :=
      (hppow n _).symm.trans ((congrArg pts ((map_nsmul Ψ.symm n ξ).symm.trans
        ((congrArg Ψ.symm hnξ).trans (map_zero Ψ.symm)))).trans hp0)
    have hΘn : Θ (pts (Ψ.symm ξ)) ^ n = 1 := (map_pow Θ _ n).symm.trans ((congrArg Θ hu0).trans (map_one Θ))

    have Hob4 := (h.2.2.2.1 n hn0 hpn).2 (Θ (pts (Ψ.symm ξ))) hΘn
    choose z hzn hzred using Hob4

    have Pmem : (gpts (gpts.symm (cS z))).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1 :=
      (congrArg Subtype.val (Equiv.apply_symm_apply gpts (cS z))).trans (hcS z)
    refine ⟨⟨gpts.symm (cS z), z, Pmem⟩, ⟨n, hn0, hpn, ?_⟩, ?_⟩
    ·
      exact gpts.injective ((hgpow n _).trans ((congrArg (fun t => t ^ n) (Equiv.apply_symm_apply gpts (cS z))).trans
        ((map_pow cS z n).symm.trans ((congrArg cS hzn).trans ((map_one cS).trans hg0.symm)))))
    ·
      show spF ⟨gpts.symm (cS z), z, Pmem⟩ = ξ
      exact (hspI _ ⟨z, Pmem⟩ z Pmem).trans ((congrArg (fun u => Ψ (pts.symm u))
        (hredΘ _ z (hzred.trans (hcT z).symm))).trans ((congrArg Ψ (Equiv.symm_apply_apply pts _)).trans
          (AddEquiv.apply_symm_apply Ψ ξ)))

end S_ModularCurve_XOneP_normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3
end P2MW
export P2MW.S_ModularCurve_XOneP_normFreePartFamily_exists_dom_sp_interface_twoChartModel_x1_mul_opsV3 (solution)
