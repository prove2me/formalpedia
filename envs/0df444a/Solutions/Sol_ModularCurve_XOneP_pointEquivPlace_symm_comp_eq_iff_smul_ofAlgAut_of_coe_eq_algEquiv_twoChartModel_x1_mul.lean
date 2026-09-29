-- Prove2me | solution 1 for ModularCurve.XOneP.pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/195b19d3-cf9a-54a1-a80b-996775cbab89

import Mathlib
import Theorems.Thm_ModularCurve_XOneP_mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
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
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace SigmaGen

open scoped Pointwise

section PlaceAction
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem smul_mem (σ : F ≃ₐ[K] F) (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    σ f ∈ (SemilinearAut.ofAlgAut σ • v).toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.smul_mem_pointwise_smul _ f _ hf

theorem isRational [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := (IsCurveOver.instFiniteResidue (K := K) (F := F) v).finite
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem evalAt_smul (σ : F ≃ₐ[K] F) (v : Place K F) (hv : v.IsRational)
    (hv' : (SemilinearAut.ofAlgAut σ • v).IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    (SemilinearAut.ofAlgAut σ • v).evalAt (σ f) = v.evalAt f := by
  set g := SemilinearAut.ofAlgAut σ with hg
  have hf' : σ f ∈ (g • v).toValuationSubring := smul_mem σ v hf
  apply (g • v).algebraMap_residueField_injective
  rw [(g • v).algebraMap_evalAt hv' hf']

  have h1 := SemilinearAut.smulResidueRingEquiv_algebraMap g v (v.evalAt f)
  rw [SemilinearAut.baseAut_ofAlgAut] at h1
  change _ = algebraMap K (g • v).ResidueField (v.evalAt f) at h1
  rw [← h1, v.algebraMap_evalAt hv hf]
  symm
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

end PlaceAction

end SigmaGen

open SigmaGen in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]

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

    (σ : ↥K ≃ₐ[L] ↥K)
    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))

    (ρσ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρσ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((ρσ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = σ (b : ↥K)) :
    ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
      (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ),
      ((Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) ↔
      ((Mη.pointEquivPlace.symm (SemilinearAut.ofAlgAut σbar • P)).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom (ψ.comp ρσ.symm.toRingHom)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) := by
  classical
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) := ModularCurve.isCurveOver_x1FunctionFieldBar (M * p)

  set READ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → ↥(ModularCurve.x1FunctionFieldBar (M * p)) := fun r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) => Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r)))) with hREAD
  set g : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) := SemilinearAut.ofAlgAut σbar with hg
  set fst' := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) with hfst'
  obtain ⟨EM1, EM2, EM3⟩ :=
    ModularCurve.XOneP.mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
      p M L K A j Mη eη heη

  have hread : ∀ r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), σbar (READ (ρσ.symm r)) = READ r := by
    intro r
    apply Subtype.ext
    rw [hσbar (READ (ρσ.symm r)) ((ρσ.symm r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) (hMηpin (ρσ.symm r)), ← hρσ (ρσ.symm r),
      RingEquiv.apply_symm_apply, hMηpin r]

  have hinj : ∀ x y : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _},
      x.1 ≫ eη ≫ fst' = y.1 ≫ eη ≫ fst' → x = y := by
    intro x y h
    apply Subtype.ext
    rw [← cancel_mono eη]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h
    · rw [Category.assoc, Category.assoc, heη, x.2, y.2]

  have key : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p))) (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* (AlgebraicClosure ℚ)),
      (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ fst' = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      (Mη.pointEquivPlace.symm (g • P)).1 ≫ eη ≫ fst' =
        Spec.map (CommRingCat.ofHom (ψ.comp ρσ.symm.toRingHom)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
    intro P ψ hP
    have h1 := EM1 (Mη.pointEquivPlace.symm P) ψ hP
    simp only [Equiv.apply_symm_apply] at h1

    have h2 : ∀ r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), READ r ∈ (g • P).toValuationSubring ∧ (g • P).evalAt (READ r) = ψ (ρσ.symm r) := by
      intro r
      obtain ⟨hm, hv⟩ := h1 (ρσ.symm r)
      refine ⟨?_, ?_⟩
      · rw [← hread r]; exact smul_mem σbar P hm
      · rw [← hread r, ← hv]
        exact evalAt_smul σbar P (isRational P) (isRational _) hm

    obtain ⟨ψ', hψ'⟩ :=
      ModularCurve.XOneP.exists_comp_eq_specMap_comp_iotaFin_of_jChartFin_mem_pointEquivPlace_twoChartModel_x1_mul
        p M L K A j Mη eη heη (Mη.pointEquivPlace.symm (g • P)) (by
          simpa only [Equiv.apply_symm_apply] using (h2 (ModularCurve.TwoChart.jChartFin A (↥K) j)).1)

    have h3 := EM1 (Mη.pointEquivPlace.symm (g • P)) ψ' hψ'
    simp only [Equiv.apply_symm_apply] at h3
    have hψeq : ψ' = ψ.comp ρσ.symm.toRingHom := by
      refine RingHom.ext fun r => ?_
      rw [← (h3 r).2, (h2 r).2]
      rfl
    rw [hψ', hψeq]
  intro P ψ
  refine ⟨key P ψ, fun hP => ?_⟩

  have hA : ψ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = algebraMap A (AlgebraicClosure ℚ) := by
    refine RingHom.ext fun a => ?_
    have h3 := EM1 (Mη.pointEquivPlace.symm (g • P)) _ hP
    simp only [Equiv.apply_symm_apply] at h3
    have h4 := (h3 (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a)).2
    erw [EM3 a, Place.evalAt_algebraMap_eq] at h4

    have h5 : ρσ.symm (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a) = algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a := by
      apply ρσ.injective
      rw [RingEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hρσ, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L (↥K), AlgEquiv.commutes]
    rw [h4]
    show ψ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a) = (ψ.comp ρσ.symm.toRingHom) (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a)
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h5]
  obtain ⟨x₀, hx₀⟩ := EM2 ψ hA
  have hfwd := key (Mη.pointEquivPlace x₀) ψ (by simpa only [Equiv.symm_apply_apply] using hx₀)
  rw [← hP] at hfwd
  have heq := hinj _ _ hfwd
  have hP0 : Mη.pointEquivPlace x₀ = P := by
    have := Mη.pointEquivPlace.symm.injective heq
    exact smul_left_cancel g this
  rw [← hP0, Equiv.symm_apply_apply]
  exact hx₀

end S_ModularCurve_XOneP_pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_pointEquivPlace_symm_comp_eq_iff_smul_ofAlgAut_of_coe_eq_algEquiv_twoChartModel_x1_mul (solution)
