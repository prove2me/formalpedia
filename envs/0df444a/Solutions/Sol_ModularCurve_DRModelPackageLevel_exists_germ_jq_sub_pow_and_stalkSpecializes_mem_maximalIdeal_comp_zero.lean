-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_comp_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b41cbafd-15c3-528d-a7c2-84a1b8b21663

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
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff
import Theorems.Thm_ModularCurve_exists_qExpand_jqInt_sub_pow_eq_natCast_mul
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Definitions.Def_ModularCurve_KroneckerTransport

import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_comp_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace HorZeroLevel

open AlgebraicCurve IsLocalRing ModularCurve

private theorem crossing_mem_preimage_iotaFin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1))) :
    (pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1) ≫ 𝔓.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base n ∈
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) := by
  classical
  obtain ⟨⟨hcl, -⟩, -⟩ := 𝔓.node_pin κ (toκ.comp ρO) n
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton κ
    (𝔓.Mfib κ (toκ.comp ρO)).toBase _ (mem_closedPoints_iff.mp hcl)
  have hinv : (𝔓.efib κ (toκ.comp ρO)).base ((inv (𝔓.efib κ (toκ.comp ρO))).base
      ((pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1)).base n)) =
      (pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1)).base n := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have huκ : (pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1) ≫ 𝔓.comp κ (toκ.comp ρO) 0).base n =
      (z.left ≫ 𝔓.efib κ (toκ.comp ρO) ≫ 𝔓.comp κ (toκ.comp ρO) 0).base (IsLocalRing.closedPoint κ) := by
    simp only [Scheme.Hom.comp_apply]
    rw [← hinv, ← hz]
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨ψ, hψ⟩ := ModularCurve.DRModelPackageLevel.exists_eq_spec_map_comp_iotaFin_of_comp_base_eq N₀ q hqN 𝔓 κ
    (toκ.comp ρO) (RingHom.id κ)
    (fun c hc => by
      by_contra h
      exact ((IsLocalRing.mem_maximalIdeal c).mp hc) (isUnit_iff_ne_zero.mpr h))
    ((z.left ≫ 𝔓.efib κ (toκ.comp ρO) ≫ 𝔓.comp κ (toκ.comp ρO) 0) ≫
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))))
    (z.left ≫ 𝔓.efib κ (toκ.comp ρO) ≫ 𝔓.comp κ (toκ.comp ρO) 0)
    (by rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]) n huκ

  have h1 : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base
      ((pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1) ≫ 𝔓.comp κ (toκ.comp ρO) 0).base n) ∈
      (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤ := by
    have e1 : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base
        ((pullback.fst (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1) ≫ 𝔓.comp κ (toκ.comp ρO) 0).base n) =
        (IgusaScheme.ιFin (N₀ * q) q).base ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint κ)) := by
      rw [huκ]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun g => g.base (IsLocalRing.closedPoint κ)) hψ).trans (Scheme.Hom.comp_apply _ _ _))
    rw [e1]
    exact ⟨_, trivial, rfl⟩

  have hbc : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
    simp only [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
  show (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base _ ∈ (IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤
  rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hbc]
  simp only [Scheme.Hom.comp_apply] at h1 ⊢
  exact h1

private theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    [Nonempty U] (f : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ U x hx).hom f) = (X.germToFunctionField U).hom f := by
  change ((X.presheaf.germ U x hx) ≫ X.presheaf.stalkSpecializes _).hom f = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

private theorem natCast_mem_nonunits_of_gauss (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (W₀ : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) :
    ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ W₀.nonunits := by
  have hqLS : (q : LaurentSeries ℚ) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) q]
    exact HahnSeries.C_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  rw [ValuationSubring.mem_nonunits_iff_or]
  refine Or.inr fun hinv => ?_
  obtain ⟨x, y, hy, hxy⟩ := (hW₀ _).mp hinv

  have hinjQ : Function.Injective (coeffMap (Int.castRingHom ℚ)) := by
    intro a b hab
    ext k
    have := congrArg (fun s : LaurentSeries ℚ => s.coeff k) hab
    exact Int.cast_injective (α := ℚ) this
  have hqQ : (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ : ↥(modularFunctionFieldFull (N₀ * q))) = ((((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))⁻¹ := by
    push_cast; rfl
  have hy' : y = (q : LaurentSeries ℤ) * x := by
    apply hinjQ
    rw [map_mul, map_natCast, ← hxy, hqQ]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hqLS, one_mul]
  apply hy
  rw [hy', map_mul, map_natCast, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := ZMod q)) q, ZMod.natCast_self, map_zero,
    zero_mul]

end HorZeroLevel

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem solution

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]

    (n : ↥(pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)))
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n)) _
        (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n) trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hsp₀ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n)) :
    ∃ tF : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n),
      φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) tF) =
        ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun N₀ q - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N₀ q ^ q ∧
      ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₀).hom tF ∈ IsLocalRing.maximalIdeal _ := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨W, hW₀, -, -, -, -⟩ := ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N₀ q hqN
  obtain ⟨𝔮₀, h𝔮₀, hmem⟩ := ModularCurve.DRModelPackageLevel.exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff N₀ q hqN 𝔓
    (W 0) hW₀ (ResidueField ↥A) (toκ.comp ρO)
  obtain ⟨h, hh⟩ := ModularCurve.exists_qExpand_jqInt_sub_pow_eq_natCast_mul q
  obtain ⟨-, hjdA, -⟩ := ModularCurve.IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg (N₀ * q) q q (dvd_mul_left q N₀)

  let jdA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨⟨qExpand ℚ q jq, jqd_mem_full (N₀ * q) (dvd_mul_left q N₀)⟩, hjdA⟩
  let aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := jdA - IgusaScheme.jChartFin (N₀ * q) q ^ q
  have haLS : (((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = qExpand ℚ q jq - jq ^ q := by
    show ((((jdA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) - (((IgusaScheme.jChartFin (N₀ * q) q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q)))) ^ q :
        ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = _
    rw [IgusaScheme.coe_jChartFin, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, IgusaScheme.coe_jFull]
  let sec : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) → Γ((DRLevel.X N₀ q), ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) := fun b =>
    ((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv b)

  have hxU := HorZeroLevel.crossing_mem_preimage_iotaFin N₀ q hqN 𝔓 O ρO (ResidueField ↥A) toκ n
  have hyU : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ∈ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤) :=
    hsp₀.mem_open ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).isOpen hxU

  refine ⟨((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)) _ hxU).hom
    (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom (sec aA)), ?_, ?_⟩
  ·
    rw [HorZeroLevel.algebraMap_germ_eq_germToFunctionField]
    apply Subtype.ext
    rw [hφj aA]
    show coeffEmb (AlgebraicClosure ℚ) (((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = _
    rw [haLS, map_sub, map_pow]
    rfl
  ·
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [← Scheme.mem_basicOpen _ _ _ hyU, ← Scheme.preimage_basicOpen]
    show ¬ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ∈ (DRLevel.X N₀ q).basicOpen (sec aA))
    have hbc : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) =
        pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
      simp only [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
    rw [← Scheme.Hom.comp_apply, Category.assoc, hbc, Scheme.Hom.comp_apply]
    erw [h𝔮₀]
    show ¬ ((IgusaScheme.ιFin (N₀ * q) q).base 𝔮₀ ∈ (DRLevel.X N₀ q).basicOpen (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv _))
    rw [← Scheme.image_basicOpen, basicOpen_eq_of_affine]
    rintro ⟨𝔮, h𝔮, he⟩
    have hinj : Function.Injective (IgusaScheme.ιFin (N₀ * q) q).base := (IgusaScheme.ιFin (N₀ * q) q).isOpenEmbedding.injective
    rw [hinj he] at h𝔮

    apply h𝔮
    apply (hmem aA).mpr
    have hqnu := HorZeroLevel.natCast_mem_nonunits_of_gauss N₀ q (W 0) hW₀
    have hqLS : (q : LaurentSeries ℚ) ≠ 0 := by
      rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) q]
      exact HahnSeries.C_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    have hq0 : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := by
      intro h0
      apply hqLS
      have := congrArg (fun z : ↥(modularFunctionFieldFull (N₀ * q)) => (z : LaurentSeries ℚ)) h0
      simpa using this

    have hcl : ∀ s : LaurentSeries ℤ, coeffMap (Int.castRingHom ℚ) s = laurentMap (Int.castRingHom ℚ) s := fun s => by
      ext k; rfl
    have ha : (((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) * laurentMap (Int.castRingHom ℚ) h := by
      rw [haLS, ← laurentMap_jqInt, ← laurentMap_qExpand, ← map_pow, ← map_sub, hh, map_mul, map_natCast]
    have hgLS : (((((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))))⁻¹ : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) =
        coeffMap (Int.castRingHom ℚ) h := by
      push_cast
      rw [ha, hcl, mul_comm, ← mul_assoc, inv_mul_cancel₀ hqLS, one_mul]
    have hgW : ((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))))⁻¹ ∈ W 0 :=
      (hW₀ _).mpr ⟨h, 1, by simp, by rw [map_one, mul_one, hgLS]⟩
    have haq : ((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
        ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) * (((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))))⁻¹) := by
      exact ((mul_comm _ _).trans (inv_mul_cancel_right₀ hq0 _)).symm
    rw [haq, ValuationSubring.mem_nonunits_iff, map_mul]
    calc (W 0).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) * (W 0).valuation (((aA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))))⁻¹)
        ≤ (W 0).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) * 1 :=
          mul_le_mul_right (((W 0).valuation_le_one_iff _).mpr hgW) _
      _ = (W 0).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) := mul_one _
      _ < 1 := (ValuationSubring.mem_nonunits_iff (W 0)).mp hqnu

end S_ModularCurve_DRModelPackageLevel_exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_comp_zero
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_comp_zero (solution)
