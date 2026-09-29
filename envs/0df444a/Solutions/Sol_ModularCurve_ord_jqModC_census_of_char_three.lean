-- Prove2me | solution 1 for ModularCurve.ord_jqModC_census_of_char_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/58cea183-e93e-5b7f-a039-b9245e032764

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three
import Theorems.Thm_Function_orbitCensus_of_dihedralThree_relations
import Theorems.Thm_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jqModC_census_of_char_three
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve

namespace P2MKcCEN3

section Cyclic

variable {A : Type*} [AddCommGroup A] {N : ℕ} [NeZero N]

abbrev CycN (A : Type*) [AddCommGroup A] (N : ℕ) : Type _ :=
  {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N}

scoped instance finite_of_cycN (H : CycN A N) : Finite H.1 :=
  Nat.finite_of_card_ne_zero (by rw [H.2.2]; exact NeZero.ne N)

theorem exists_eq_zmultiples (H : CycN A N) :
    ∃ g : A, addOrderOf g = N ∧ H.1 = AddSubgroup.zmultiples g := by
  obtain ⟨hc, hcard⟩ := H.2
  haveI := hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_ofOrder_eq_natCard (α := H.1)
  have hord : addOrderOf (g : A) = N := by
    have h1 : addOrderOf (g : A) = addOrderOf g := AddSubgroup.addOrderOf_coe g
    rw [h1, hg]; exact hcard
  refine ⟨(g : A), hord, ?_⟩
  have hle : AddSubgroup.zmultiples (g : A) ≤ H.1 := AddSubgroup.zmultiples_le_of_mem g.2
  have hcard' : Nat.card (AddSubgroup.zmultiples (g : A)) = N := by
    rw [Nat.card_zmultiples, hord]
  exact (AddSubgroup.eq_of_le_of_card_ge hle (by rw [hcard', hcard])).symm

theorem cycN_mk_mem (g : A) (hg : addOrderOf g = N) :
    IsAddCyclic (AddSubgroup.zmultiples g) ∧ Nat.card (AddSubgroup.zmultiples g) = N :=
  ⟨AddSubgroup.isAddCyclic_zmultiples g, by rw [Nat.card_zmultiples, hg]⟩

theorem cycN_ext {H H' : CycN A N} (h : H.1 = H'.1) : H = H' := Subtype.ext h

noncomputable def mapC (φ : A →+ A) (hφ : Function.Injective φ) (H : CycN A N) : CycN A N :=
  ⟨H.1.map φ, by
    obtain ⟨g, hg, hH⟩ := exists_eq_zmultiples H
    rw [hH, AddMonoidHom.map_zmultiples]
    exact cycN_mk_mem (φ g) (by rw [← hg]; exact addOrderOf_injective φ hφ g)⟩

@[scoped simp] theorem mapC_val (φ : A →+ A) (hφ : Function.Injective φ) (H : CycN A N) :
    (mapC φ hφ H).1 = H.1.map φ := rfl

theorem mapC_mapC (φ ψ : A →+ A) (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (H : CycN A N) :
    mapC φ hφ (mapC ψ hψ H) = mapC (φ.comp ψ) (hφ.comp hψ) H :=
  cycN_ext (by simp [AddSubgroup.map_map])

theorem mapC_congr {φ ψ : A →+ A} (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (h : φ = ψ)
    (H : CycN A N) : mapC φ hφ H = mapC ψ hψ H := by subst h; rfl

theorem mapC_id' {φ : A →+ A} (hφ : Function.Injective φ) (h : ∀ a, φ a = a) (H : CycN A N) :
    mapC φ hφ H = H := by
  apply cycN_ext
  have : φ = AddMonoidHom.id A := AddMonoidHom.ext h
  simp [this, AddSubgroup.map_id]

theorem mapC_neg' {φ : A →+ A} (hφ : Function.Injective φ) (h : ∀ a, φ a = -a) (H : CycN A N) :
    mapC φ hφ H = H := by
  apply cycN_ext
  obtain ⟨g, hg, hH⟩ := exists_eq_zmultiples H
  simp only [mapC_val, hH, AddMonoidHom.map_zmultiples, h, AddSubgroup.zmultiples_neg]

theorem mapC_eq_of_map_le {φ : A →+ A} (hφ : Function.Injective φ) (H H' : CycN A N)
    (h : H.1.map φ ≤ H'.1) : mapC φ hφ H = H' := by
  apply cycN_ext
  rw [mapC_val]
  exact AddSubgroup.eq_of_le_of_card_ge h (by rw [H'.2.2]; exact ((mapC φ hφ H).2.2).ge)

theorem finite_cycN [Finite (Submodule.torsionBy ℤ A N)] : Finite (CycN A N) := by
  have hsub : ∀ (H : CycN A N) (x : A), x ∈ H.1 → x ∈ Submodule.torsionBy ℤ A N := by
    intro H x hx
    rw [Submodule.mem_torsionBy_iff]
    have h0 : addOrderOf (⟨x, hx⟩ : H.1) ∣ Nat.card H.1 := addOrderOf_dvd_natCard _
    have h1 : addOrderOf x ∣ N := by
      have hc : Nat.card H.1 = N := H.2.2
      rw [hc, AddSubgroup.addOrderOf_mk] at h0
      exact h0
    rw [natCast_zsmul]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp h1
  refine Finite.of_injective
    (fun H : CycN A N => ({x : Submodule.torsionBy ℤ A N | (x : A) ∈ H.1} : Set _)) ?_
  intro H H' h
  simp only at h
  apply cycN_ext
  ext x
  constructor
  · intro hx
    have : (⟨x, hsub H x hx⟩ : Submodule.torsionBy ℤ A N) ∈
        ({x : Submodule.torsionBy ℤ A N | (x : A) ∈ H'.1} : Set _) := by
      rw [← h]; exact hx
    exact this
  · intro hx
    have : (⟨x, hsub H' x hx⟩ : Submodule.torsionBy ℤ A N) ∈
        ({x : Submodule.torsionBy ℤ A N | (x : A) ∈ H.1} : Set _) := by
      rw [h]; exact hx
    exact this

end Cyclic

section Operators

variable {A : Type*} [AddCommGroup A] {N : ℕ} [NeZero N]
  (α β : A →+ A) (hαα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
  (hαβ : ∀ T, α (β T) = β (β (α T)))

include hαα in
theorem α_injective : Function.Injective α := fun a b h => by
  have h' := congrArg α h
  rwa [hαα, hαα, neg_inj] at h'

include hβ in
theorem βββ (T : A) : β (β (β T)) = T := by
  have h1 := hβ (β T)
  have h2 := congrArg β (hβ T)
  rw [map_add, map_add, map_zero] at h2

  have h3 := hβ T

  have : β (β (β T)) - T = (β (β (β T)) + β (β T) + β T) - (β (β T) + β T + T) := by abel
  rw [h1, h3, sub_zero] at this
  exact sub_eq_zero.mp this

include hβ in
theorem β_injective : Function.Injective β := fun a b h => by
  have h' := congrArg (fun x => β (β x)) h
  simp only [βββ β hβ] at h'
  exact h'

noncomputable def aX (H : CycN A N) : CycN A N := mapC α (α_injective α hαα) H

noncomputable def bX (H : CycN A N) : CycN A N := mapC β (β_injective β hβ) H

theorem aX_val (H : CycN A N) : (aX α hαα H).1 = H.1.map α := rfl
theorem bX_val (H : CycN A N) : (bX β hβ H).1 = H.1.map β := rfl

theorem aX_aX (H : CycN A N) : aX α hαα (aX α hαα H) = H := by
  unfold aX
  rw [mapC_mapC]
  exact mapC_neg' _ (fun a => by simp [hαα]) H

theorem bX_bX_bX (H : CycN A N) : bX β hβ (bX β hβ (bX β hβ H)) = H := by
  unfold bX
  rw [mapC_mapC, mapC_mapC]
  exact mapC_id' _ (fun a => by simp [βββ β hβ]) H

include hαβ in
theorem aX_bX (H : CycN A N) : aX α hαα (bX β hβ H) = bX β hβ (bX β hβ (aX α hαα H)) := by
  unfold aX bX
  rw [mapC_mapC, mapC_mapC, mapC_mapC]
  exact mapC_congr _ _ (AddMonoidHom.ext fun T => by simp [hαβ]) H

theorem mapC_six {m : A →+ A} (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨
      m = α.comp β ∨ m = α.comp (β.comp β)) (hminj : Function.Injective m) (H : CycN A N) :
    mapC m hminj H = H ∨ mapC m hminj H = aX α hαα H ∨ mapC m hminj H = bX β hβ H ∨
      mapC m hminj H = bX β hβ (bX β hβ H) ∨ mapC m hminj H = aX α hαα (bX β hβ H) ∨
      mapC m hminj H = aX α hαα (bX β hβ (bX β hβ H)) := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (mapC_id' _ (fun _ => rfl) H)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    unfold bX; rw [mapC_mapC]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    unfold aX bX; rw [mapC_mapC]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    unfold aX bX; rw [mapC_mapC, mapC_mapC]
    exact mapC_congr _ _ (by ext; rfl) H

include hαα hβ in
theorem injective_six {m : A →+ A} (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨
      m = α.comp β ∨ m = α.comp (β.comp β)) : Function.Injective m := by
  have hαi := α_injective α hαα
  have hβi := β_injective β hβ
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun a b h => h
  · exact hαi
  · exact hβi
  · exact hβi.comp hβi
  · exact hαi.comp hβi
  · exact hαi.comp (hβi.comp hβi)

theorem exists_six_of_mem (H H' : CycN A N)
    (h : H' = H ∨ H' = aX α hαα H ∨ H' = bX β hβ H ∨ H' = bX β hβ (bX β hβ H) ∨
      H' = aX α hαα (bX β hβ H) ∨ H' = aX α hαα (bX β hβ (bX β hβ H))) :
    ∃ (m : A →+ A) (hm : m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨
      m = α.comp β ∨ m = α.comp (β.comp β)), H'.1 = H.1.map m := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨AddMonoidHom.id _, Or.inl rfl, by simp⟩
  · exact ⟨α, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨β, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · exact ⟨β.comp β, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by simp [bX_val, AddSubgroup.map_map]⟩
  · exact ⟨α.comp β, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      by simp [aX_val, bX_val, AddSubgroup.map_map]⟩
  · exact ⟨α.comp (β.comp β), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
      by simp [aX_val, bX_val, AddSubgroup.map_map]⟩

include hαα hβ in

theorem exists_addOrderOf_eq_and_β_ne_nsmul (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (e : ZMod p × ZMod p ≃+ Submodule.torsionBy ℤ A p) (hαβ' : ∀ T, α (β T) = β (β (α T))) :
    ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, β a ≠ k • a := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon

  set P : A := (e (1, 0) : A) with hP
  set Q : A := (e (0, 1) : A) with hQ
  have hmem : ∀ v : ZMod p × ZMod p, (p : ℤ) • (e v : A) = 0 := fun v =>
    (Submodule.mem_torsionBy_iff _ _).mp (e v).2
  have hval : ∀ v : ZMod p × ZMod p, (e v : A) = (v.1.val : ℤ) • P + (v.2.val : ℤ) • Q := by
    intro v
    have : v = (v.1.val : ℤ) • ((1, 0) : ZMod p × ZMod p) + (v.2.val : ℤ) • ((0, 1) : ZMod p × ZMod p) := by
      ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_zsmul, map_zsmul]
    simp [hP, hQ]
  have hne : ∀ v : ZMod p × ZMod p, v ≠ 0 → (e v : A) ≠ 0 := by
    intro v hv h0
    apply hv
    apply e.injective
    rw [map_zero]
    exact Subtype.ext h0
  have hord : ∀ v : ZMod p × ZMod p, v ≠ 0 → addOrderOf (e v : A) = p := by
    intro v hv
    apply addOrderOf_eq_prime _ (hne v hv)
    rw [← natCast_zsmul]; exact hmem v

  have hcoord : ∀ m n : ℤ, m • P + n • Q = 0 → (m : ZMod p) = 0 ∧ (n : ZMod p) = 0 := by
    intro m n h
    have h1 : (e ((m : ZMod p), (n : ZMod p)) : A) = m • P + n • Q := by
      have : ((m : ZMod p), (n : ZMod p)) = m • ((1, 0) : ZMod p × ZMod p) + n • ((0, 1) : ZMod p × ZMod p) := by
        ext <;> simp
      rw [this, map_add, map_zsmul, map_zsmul]
      simp [hP, hQ]
    rw [h] at h1
    have h2 : ((m : ZMod p), (n : ZMod p)) = 0 := by
      apply e.injective; rw [map_zero]; exact Subtype.ext h1
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

  have h10 : ((1, 0) : ZMod p × ZMod p) ≠ 0 := by simp
  have h01 : ((0, 1) : ZMod p × ZMod p) ≠ 0 := by simp
  have h11 : ((1, 1) : ZMod p × ZMod p) ≠ 0 := by simp
  obtain ⟨k₁, hk₁⟩ := hcon P (hord (1, 0) h10)
  obtain ⟨k₂, hk₂⟩ := hcon Q (hord (0, 1) h01)
  have hPQ : (e (1, 1) : A) = P + Q := by
    have : ((1, 1) : ZMod p × ZMod p) = (1, 0) + (0, 1) := by simp
    rw [this, map_add]; rfl
  obtain ⟨k₃, hk₃⟩ := hcon (P + Q) (hPQ ▸ hord (1, 1) h11)

  have hk : (k₁ : ZMod p) = k₃ ∧ (k₂ : ZMod p) = k₃ := by
    have hsum : k₁ • P + k₂ • Q = k₃ • P + k₃ • Q := by
      rw [← hk₁, ← hk₂, ← smul_add, ← hk₃, map_add]
    have h1 : ((k₁ : ℤ) - k₃) • P + ((k₂ : ℤ) - k₃) • Q = 0 := by
      rw [sub_zsmul, sub_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]
      calc _ = (k₁ • P + k₂ • Q) - (k₃ • P + k₃ • Q) := by abel
        _ = 0 := by rw [hsum, sub_self]
    obtain ⟨ha, hb⟩ := hcoord _ _ h1
    push_cast at ha hb
    exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩

  have hzs : ∀ (m n : ℤ) (v : A), (p : ℤ) • v = 0 → (m : ZMod p) = n → m • v = n • v := by
    intro m n v hv hmn
    obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n m p).mp hmn.symm
    have : m = n + p * c := by linarith
    rw [this, add_zsmul, mul_comm, mul_zsmul, hv, zsmul_zero, add_zero]
  have hpP : (p : ℤ) • P = 0 := hmem (1, 0)
  have hpQ : (p : ℤ) • Q = 0 := hmem (0, 1)

  have hβQ : β Q = (k₁ : ℤ) • Q := by
    rw [hk₂, ← natCast_zsmul]
    exact hzs _ _ Q hpQ (by push_cast; rw [hk.2, hk.1])
  have hβP : β P = (k₁ : ℤ) • P := by rw [hk₁, natCast_zsmul]

  have hαP_mem : α P ∈ Submodule.torsionBy ℤ A p := by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hpP, map_zero]
  obtain ⟨w, hw⟩ : ∃ w : ZMod p × ZMod p, (e w : A) = α P := ⟨e.symm ⟨α P, hαP_mem⟩, by simp⟩
  have hβαP : β (α P) = (k₁ : ℤ) • α P := by
    rw [← hw, hval w, map_add, map_zsmul, map_zsmul, hβP, hβQ, smul_add, smul_comm _ (k₁ : ℤ) P,
      smul_comm _ (k₁ : ℤ) Q]

  have hrel : ((k₁ : ℤ) * k₁ - k₁) • α P = 0 := by
    have h := hαβ' P
    rw [hβP, map_zsmul, hβαP, map_zsmul, hβαP, ← mul_zsmul] at h
    rw [sub_zsmul, ← h]; simp
  have hordαP : addOrderOf (α P) = p := by
    rw [← hw]; apply hord; intro h0; rw [h0, map_zero] at hw
    exact (hne (1, 0) h10) (by
      have := (α_injective α hαα) (a₁ := 0) (a₂ := P) (by rw [map_zero]; exact hw)
      exact this.symm)
  have hdvd1 : ((k₁ : ZMod p) * k₁ - k₁) = 0 := by
    have h := (addOrderOf_dvd_iff_zsmul_eq_zero (x := α P)).mpr hrel
    rw [hordαP] at h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((k₁ : ℤ) * k₁ - k₁) p).mpr h
    push_cast at this
    exact this

  have hdvd2 : ((k₁ : ZMod p) * k₁ + k₁ + 1) = 0 := by
    have h := hβ P
    rw [hβP, map_zsmul, hβP, ← mul_zsmul] at h
    have h' : ((k₁ : ℤ) * k₁ + k₁ + 1) • P = 0 := by
      rw [add_zsmul, add_zsmul, one_zsmul]; exact h
    have h2 := (addOrderOf_dvd_iff_zsmul_eq_zero (x := P)).mpr h'
    rw [hord (1, 0) h10] at h2
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((k₁ : ℤ) * k₁ + k₁ + 1) p).mpr h2
    push_cast at this
    exact this

  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    have : (3 : ZMod p) = 4 * ((k₁ : ZMod p) * k₁ + k₁ + 1) - (2 * k₁ + 1) ^ 2 := by ring
    have h2k : (2 * (k₁ : ZMod p) + 1) = ((k₁ : ZMod p) * k₁ + k₁ + 1) - ((k₁ : ZMod p) * k₁ - k₁) := by ring
    push_cast
    rw [this, h2k, hdvd1, hdvd2]; ring
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)

end Operators

section CharThree

variable {K : Type*} [Field K] [DecidableEq K]

abbrev E0 (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

theorem three_eq_zero [CharP K 3] : (3 : K) = 0 := by simpa using CharP.cast_eq_zero K 3

theorem two_ne_zero' [CharP K 3] : (2 : K) ≠ 0 := by
  intro h
  have h3 : (3 : K) = 0 := three_eq_zero
  have : (1 : K) = 0 := by linear_combination h3 - h
  exact one_ne_zero this

theorem E0_Δ : (E0 K).Δ = 64 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem E0_c₄ : (E0 K).c₄ = 48 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem isElliptic_E0 [CharP K 3] : (E0 K).IsElliptic := by
  refine ⟨?_⟩
  rw [E0_Δ, isUnit_iff_ne_zero]
  have h3 : (3 : K) = 0 := three_eq_zero
  intro h
  have : (1 : K) = 0 := by linear_combination h - 21 * h3
  exact one_ne_zero this

theorem E0_j [CharP K 3] : letI := isElliptic_E0 (K := K); (E0 K).j = 0 := by
  letI := isElliptic_E0 (K := K)
  rw [WeierstrassCurve.j_eq_zero_iff, E0_c₄]
  have h3 : (3 : K) = 0 := three_eq_zero
  linear_combination 16 * h3

theorem baseChange_self (W : WeierstrassCurve K) : (W⁄K) = W.toAffine := by
  show (W.baseChange K).toAffine = W.toAffine
  rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]

theorem eq_of_heq_heq {W : WeierstrassCurve K} {γ : VariableChange K} {T : W.toAffine.Point}
    {X Y : W.toAffine.Point} (h1 : HEq (Point.vcInvFun γ W.toAffine T) X)
    (h2 : HEq (Point.vcInvFun γ W.toAffine T) Y) : X = Y :=
  eq_of_heq (h1.symm.trans h2)

theorem forall_exists_heq_iff_map_eq {W : WeierstrassCurve K} (γ : VariableChange K)
    (φ : W.toAffine.Point →+ W.toAffine.Point) (hφ : ∀ T, HEq (Point.vcInvFun γ W.toAffine T) (φ T))
    (hinj : Function.Injective φ) (H : AddSubgroup W.toAffine.Point) [Finite H] :
    (∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ W.toAffine T) T') ↔ H.map φ = H := by
  constructor
  · intro hH
    have hle : H.map φ ≤ H := by
      intro y hy
      rw [AddSubgroup.mem_map] at hy
      obtain ⟨T, hT, rfl⟩ := hy
      obtain ⟨T', hT', hheq⟩ := hH T hT
      rwa [eq_of_heq_heq (hφ T) hheq]
    exact AddSubgroup.eq_of_le_of_card_ge hle
      (Nat.card_congr (H.equivMapOfInjective _ hinj).toEquiv).le
  · intro hH T hT
    exact ⟨φ T, by rw [← hH]; exact AddSubgroup.mem_map_of_mem _ hT, hφ T⟩

theorem map_le_of_forall_exists_heq {W : WeierstrassCurve K} (γ : VariableChange K)
    (φ : W.toAffine.Point →+ W.toAffine.Point)
    (hφ : (∀ T, HEq (Point.vcInvFun γ W.toAffine T) (φ T)) ∨
      (∀ T, HEq (Point.vcInvFun γ W.toAffine T) (-(φ T))))
    (H H' : AddSubgroup W.toAffine.Point)
    (hH : ∀ T ∈ H, ∃ T' ∈ H', HEq (Point.vcInvFun γ W.toAffine T) T') : H.map φ ≤ H' := by
  intro y hy
  rw [AddSubgroup.mem_map] at hy
  obtain ⟨T, hT, rfl⟩ := hy
  obtain ⟨T', hT', hheq⟩ := hH T hT
  rcases hφ with hφ | hφ
  · rwa [eq_of_heq_heq (hφ T) hheq]
  · have : -(φ T) = T' := eq_of_heq_heq (hφ T) hheq
    have h' : φ T = -T' := by rw [← this, neg_neg]
    rw [h']; exact H'.neg_mem hT'

end CharThree

section Assembly

variable {A : Type*} [AddCommGroup A] {N : ℕ} [NeZero N]

theorem natCard_subtype_eq_card_filter {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] :
    Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Assembly

end P2MKcCEN3
p2m_reactivate "P2MW.S_ModularCurve_ord_jqModC_census_of_char_three.P2MKcCEN3"

open P2MKcCEN3 in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 3] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (S : Finset (Place K (modularFunctionFieldFullC K N)))
    (hS : ∀ P, P ∈ S ↔ 0 < P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)) :
    (∀ P ∈ S, P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 2 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6) ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1 ∨
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 3).card = nuTwo N ∧
    (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 1).card +
      2 * (S.filter fun P =>
        P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 2).card =
      nuThree N := by
  classical
  set J : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩ with hJdef

  have h2 : (2 : K) ≠ 0 := two_ne_zero'
  obtain ⟨i0, hi0⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) two_pos
  have hi0ne : i0 ≠ 0 := by
    rintro rfl
    norm_num at hi0
  set i : Kˣ := Units.mk0 i0 hi0ne with hidef
  have hi : (i : K) ^ 2 = -1 := by rw [hidef, Units.val_mk0, hi0]
  haveI hE : (E0 K).IsElliptic := isElliptic_E0
  have hj : (E0 K).j = 0 := E0_j

  have hS' : ∀ P, P ∈ S ↔ 0 < P.ord (J - algebraMap K (modularFunctionFieldFullC K N) (0 : K)) := by
    intro P; rw [map_zero, sub_zero]; exact hS P
  obtain ⟨f, hfS, hSf, hff, hord⟩ :=
    ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC K N hN 0 (E0 K) hj
      S hS'
  simp only [map_zero, sub_zero] at hord

  obtain ⟨α, β, hα, hβv, hαα, hβ, hαβ, hstab, hsix⟩ :=
    WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three i hi

  obtain ⟨e⟩ : Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E0 K).toAffine.Point N) := by
    have h := (E0 K).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) hN
    rwa [baseChange_self] at h
  haveI : Finite (Submodule.torsionBy ℤ (E0 K).toAffine.Point N) := Finite.of_equiv _ e.toEquiv
  haveI : Finite (CycN (E0 K).toAffine.Point N) := finite_cycN
  letI : Fintype (CycN (E0 K).toAffine.Point N) := Fintype.ofFinite _

  have hc : ∀ H H' : CycN (E0 K).toAffine.Point N, f H = f H' ↔
      (H' = H ∨ H' = aX α hαα H ∨ H' = bX β hβ H ∨ H' = bX β hβ (bX β hβ H) ∨
        H' = aX α hαα (bX β hβ H) ∨ H' = aX α hαα (bX β hβ (bX β hβ H))) := by
    intro H H'
    rw [hff]
    constructor
    · rintro ⟨γ, hγ, hHH'⟩
      obtain ⟨m, hm, hmγ⟩ := hstab γ hγ
      have hminj : Function.Injective m := injective_six α β hαα hβ hm
      have hle : H.1.map m ≤ H'.1 := map_le_of_forall_exists_heq γ m hmγ H.1 H'.1 hHH'
      have hEq : mapC m hminj H = H' := mapC_eq_of_map_le hminj H H' hle
      rw [← hEq]
      exact mapC_six α β hαα hβ hm hminj H
    · intro h
      obtain ⟨m, hm, hH'⟩ := exists_six_of_mem α β hαα hβ H H' h
      obtain ⟨γ, hγ, hmγ⟩ := hsix m hm
      refine ⟨γ, hγ, fun T hT => ⟨m T, ?_, hmγ T⟩⟩
      rw [hH']; exact AddSubgroup.mem_map_of_mem _ hT

  have hSG : ∀ p, p ∈ S ↔ ∃ x, f x = p :=
    fun p => ⟨fun hp => hSf p hp, fun ⟨x, hx⟩ => hx ▸ hfS x⟩
  obtain ⟨hsize, hodd, h12⟩ := Function.orbitCensus_of_dihedralThree_relations
    (aX α hαα) (bX β hβ) (aX_aX α hαα) (bX_bX_bX β hβ) (aX_bX α β hαα hβ hαβ) f hc S hSG

  have hordF : ∀ H : CycN (E0 K).toAffine.Point N,
      (f H).ord J = ((Finset.univ.filter fun H' => f H' = f H).card : ℤ) := by
    intro H
    rw [hJdef, hord H, natCard_subtype_eq_card_filter]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨H, rfl⟩ := hSf P hP
    rw [hordF]
    rcases hsize H with h | h | h | h <;> simp [h]
  ·
    have hcongr : (S.filter fun P => P.ord J = 1 ∨ P.ord J = 3) =
        S.filter fun p => (Finset.univ.filter fun y => f y = p).card = 1 ∨
          (Finset.univ.filter fun y => f y = p).card = 3 := by
      apply Finset.filter_congr
      intro P hP
      obtain ⟨H, rfl⟩ := hSf P hP
      rw [hordF]; norm_cast
    rw [hcongr, hodd, ← WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
      (-1 : K) (by simp) i hi h2 N hN, ← natCard_subtype_eq_card_filter]
    refine Nat.card_congr ⟨fun H => ⟨H.1.1, H.1.2.1, H.1.2.2, ?_⟩, fun H => ⟨⟨H.1, H.2.1, H.2.2.1⟩, ?_⟩,
      fun H => rfl, fun H => rfl⟩
    · haveI : Finite H.1.1 := finite_of_cycN H.1
      rw [forall_exists_heq_iff_map_eq _ α hα (α_injective α hαα)]
      exact congrArg Subtype.val H.2
    · haveI : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [H.2.2.1]; exact NeZero.ne N)
      apply cycN_ext
      rw [aX_val]
      exact (forall_exists_heq_iff_map_eq _ α hα (α_injective α hαα) H.1).mp H.2.2.2
  ·
    have hcongr1 : (S.filter fun P => P.ord J = 1) =
        S.filter fun p => (Finset.univ.filter fun y => f y = p).card = 1 := by
      apply Finset.filter_congr
      intro P hP
      obtain ⟨H, rfl⟩ := hSf P hP
      rw [hordF]; norm_cast
    have hcongr2 : (S.filter fun P => P.ord J = 2) =
        S.filter fun p => (Finset.univ.filter fun y => f y = p).card = 2 := by
      apply Finset.filter_congr
      intro P hP
      obtain ⟨H, rfl⟩ := hSf P hP
      rw [hordF]; norm_cast

    have hns : ∀ p : ℕ, p.Prime → p ∣ N →
        ∃ a : (E0 K).toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, β a ≠ k • a := by
      intro p hp hpN
      have hpK : (p : K) ≠ 0 := by
        obtain ⟨c, rfl⟩ := hpN
        intro h0; apply hN; push_cast; rw [h0, zero_mul]
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact hpK (by exact_mod_cast (three_eq_zero (K := K)))
      obtain ⟨ep⟩ : Nonempty (ZMod p × ZMod p ≃+ Submodule.torsionBy ℤ (E0 K).toAffine.Point p) := by
        have h := (E0 K).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) hpK
        rwa [baseChange_self] at h
      exact exists_addOrderOf_eq_and_β_ne_nsmul α β hαα hβ p hp hp3 ep hαβ
    rw [hcongr1, hcongr2, h12,
      ← AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree
        N e β hβ hns, ← natCard_subtype_eq_card_filter]
    refine Nat.card_congr ⟨fun H => ⟨H.1.1, H.1.2.1, H.1.2.2, ?_⟩, fun H => ⟨⟨H.1, H.2.1, H.2.2.1⟩, ?_⟩,
      fun H => rfl, fun H => rfl⟩
    · exact congrArg Subtype.val H.2
    · exact cycN_ext H.2.2.2

end S_ModularCurve_ord_jqModC_census_of_char_three
end P2MW
export P2MW.S_ModularCurve_ord_jqModC_census_of_char_three (solution)
