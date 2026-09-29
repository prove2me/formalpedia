-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a43cdecf-3371-5f38-a79c-6dfdea4aff62

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_transcendental
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_ModularCurve_card_roots_fibrePoly_of_monic
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluQuotient_j_mem_of_mem
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace S13K2

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem oddOrderSummingSet_coords_mem (L : Subfield F) {n : ℕ} {Q : W.toAffine.Point}
    (hord : addOrderOf Q = 2 * n + 1)
    (htors : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (2 * n + 1) • (Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L) :
    ∀ P ∈ W.oddOrderSummingSet Q n, P.1 ∈ L ∧ P.2 ∈ L := by
  intro P hP
  obtain ⟨k, hk1, hkn, hkP⟩ := W.mem_oddOrderSummingSet.mp hP
  have hkQne : k • Q ≠ 0 := by
    intro h
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hord] at h
    exact absurd (Nat.le_of_dvd hk1 h) (by omega)
  rcases hkQ : (k • Q) with _ | ⟨x, y, hns⟩
  · exact absurd hkQ hkQne
  have hQd : (2 * n + 1) • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
  have hd : (2 * n + 1) • (Point.some x y hns : W.toAffine.Point) = 0 := by
    rw [← hkQ, smul_comm, hQd, smul_zero]
  rw [← hkP, hkQ]
  exact htors x y hns hd

theorem exists_generator_of_isAddCyclic {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (hc : IsAddCyclic H) {m : ℕ} (hm : Nat.card H = m) :
    ∃ g : G, AddSubgroup.zmultiples g = H ∧ addOrderOf g = m := by
  obtain ⟨⟨g, hgH⟩, hg⟩ := hc.exists_generator
  have hzm : AddSubgroup.zmultiples g = H := by
    apply le_antisymm (AddSubgroup.zmultiples_le.mpr hgH)
    intro x hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨g, hzm, ?_⟩
  rw [← Nat.card_zmultiples g, hzm, hm]

end S13K2

open S13K2 in
theorem solution
    {N : ℕ} [NeZero N] (hN : Odd N) (data : ModularCurve.ModularPolynomialData N)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic] (ht : Transcendental ℚ W.j)
    (L : Subfield (HahnSeries ℚ (AlgebraicClosure ℚ)))
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (htors : ∀ (x y : HahnSeries ℚ (AlgebraicClosure ℚ)) (h : W.toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hr : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot r) :
    r ∈ L := by

  haveI hK : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat
  haveI : CharZero (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    (RingHom.charZero_iff (HahnSeries.C (R := AlgebraicClosure ℚ) (Γ := ℚ)).injective).mp inferInstance
  obtain ⟨n, rfl⟩ := hN
  have h2 : (2 : HahnSeries ℚ (AlgebraicClosure ℚ)) ≠ 0 := two_ne_zero
  have hNK : ((2 * n + 1 : ℕ) : HahnSeries ℚ (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set Φj := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)
    with hΦj
  have hΦjm : Φj.Monic := data.monic.map _

  let B := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2 * n + 1}
  have hBcard : Nat.card B = ModularCurve.dedekindPsi (2 * n + 1) :=
    WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
      (F := HahnSeries ℚ (AlgebraicClosure ℚ)) (K := HahnSeries ℚ (AlgebraicClosure ℚ)) W hNK
  have hψpos : 0 < ModularCurve.dedekindPsi (2 * n + 1) := by
    unfold ModularCurve.dedekindPsi
    refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
    · simp [Nat.mem_divisors]
    · simp
  haveI : Finite B := Nat.finite_of_card_ne_zero (hBcard ▸ hψpos.ne')
  haveI : Fintype B := Fintype.ofFinite _

  have hgen : ∀ H : B, ∃ g : W.toAffine.Point,
      AddSubgroup.zmultiples g = H.1 ∧ addOrderOf g = 2 * n + 1 :=
    fun H => exists_generator_of_isAddCyclic H.1 H.2.1 H.2.2
  choose gen hgenH hgenord using hgen
  have hΔgen : ∀ H : B, (W.veluQuotient (W.oddOrderSummingSet (gen H) n)).Δ ≠ 0 := fun H =>
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero h2 W n (gen H) (hgenord H)
  let jH : B → HahnSeries ℚ (AlgebraicClosure ℚ) := fun H =>
    haveI : (W.veluQuotient (W.oddOrderSummingSet (gen H) n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (hΔgen H)⟩
    (W.veluQuotient (W.oddOrderSummingSet (gen H) n)).j

  have hjHmem : ∀ H : B, jH H ∈ L := fun H =>
    WeierstrassCurve.veluQuotient_j_mem_of_mem W L _ h₁ h₂ h₃ h₄ h₆
      (oddOrderSummingSet_coords_mem W L (hgenord H) htors) (hΔgen H)

  have hjHroot : ∀ H : B, Φj.IsRoot (jH H) := fun H =>
    ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq W n (gen H) (hgenord H)
      (hΔgen H) data

  have hjHinj : Function.Injective jH := by
    intro H H' hjeq
    have hz := WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental W ht n (gen H) (gen H')
      (hgenord H) (hgenord H') (hΔgen H) (hΔgen H') hjeq
    exact Subtype.ext ((hgenH H).symm.trans (hz.trans (hgenH H')))

  have hJcard : (Finset.univ.image jH).card = ModularCurve.dedekindPsi (2 * n + 1) := by
    rw [Finset.card_image_of_injective _ hjHinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hBcard]
  have hJsub : Finset.univ.image jH ⊆ Φj.roots.toFinset := by
    intro x hx
    obtain ⟨H, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦjm.ne_zero]
    exact hjHroot H
  have hroots : Φj.roots.toFinset = Finset.univ.image jH := by
    refine (Finset.eq_of_subset_of_card_le hJsub ?_).symm
    calc Φj.roots.toFinset.card ≤ Multiset.card Φj.roots := Multiset.toFinset_card_le _
      _ = ModularCurve.dedekindPsi (2 * n + 1) := by
          rw [hΦj, ← data.natDegree_eq]
          exact ModularCurve.card_roots_fibrePoly_of_monic (K := HahnSeries ℚ (AlgebraicClosure ℚ)) data.monic W.j
      _ = (Finset.univ.image jH).card := hJcard.symm

  have hrmem : r ∈ Φj.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦjm.ne_zero]; exact hr
  rw [hroots] at hrmem
  obtain ⟨H, -, rfl⟩ := Finset.mem_image.mp hrmem
  exact hjHmem H

end S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd (solution)
