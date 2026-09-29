-- Prove2me | solution 1 for ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3bbc220e-be40-585f-a5b2-c2fd38c73ce2

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_DualIsogenyAPI
import Definitions.Def_DualIsogenyExistence
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_veluQuotient_j_eq_of_mem_roots_fibrePoly
import Theorems.Thm_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_veluQuotient2_j_eq_of_mem_roots_fibrePoly
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet
import Theorems.Thm_AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open ModularCurve Polynomial WeierstrassCurve

namespace HCoreReduction

theorem noTors_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) {q : ℤ}
    (hA : ∀ a : A, q • a = 0 → a = 0) : ∀ b : B, q • b = 0 → b = 0 := by
  intro b hb
  have : e.symm b = 0 := hA _ (by rw [← map_zsmul, hb, map_zero])
  simpa using congrArg e this

theorem ker_bound {A B : Type*} [AddCommGroup A] [AddCommGroup B] {φ : A →+ B} {Q : A} {ℓ : ℕ}
    (hker : φ.ker = AddSubgroup.zmultiples Q) (hQ : addOrderOf Q = ℓ) :
    ∀ a, φ a = 0 → (ℓ : ℤ) • a = 0 := by
  intro a ha
  have : a ∈ AddSubgroup.zmultiples Q := by rw [← hker]; exact ha
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp this
  rw [smul_comm, natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero, zsmul_zero]

theorem nonempty_addEquiv_of_j_eq {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (V W' : WeierstrassCurve K) [V.IsElliptic] [W'.IsElliptic] (h : V.j = W'.j) :
    Nonempty (V.toAffine.Point ≃+ W'.toAffine.Point) := by
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq V W' h
  subst hC
  obtain ⟨e, -⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange V C
  exact ⟨e⟩

theorem veluPointMap2_ker_two_torsion {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h2 : (2 : K) ≠ 0) {x₀ y₀ : K}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (a : W.toAffine.Point) (ha : veluPointMap2 h2 hQ hgy hΔ a = 0) : (2 : ℤ) • a = 0 := by
  rcases a with _ | ⟨x, y, h⟩
  · exact zsmul_zero _
  · by_cases hx : x = x₀
    · subst hx

      have hgy' : 2 * y₀ + W.a₁ * x + W.a₃ = 0 := by
        have := hgy; simp only [veluGy] at this; linear_combination -this
      have h1 : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
        (Affine.equation_iff _ _).mp h.1
      have h0 : y₀ ^ 2 + W.a₁ * x * y₀ + W.a₃ * y₀ = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
        (Affine.equation_iff _ _).mp hQ
      have hfac : (y - y₀) * (y - y₀) = 0 := by linear_combination h1 - h0 - (y - y₀) * hgy'
      have hy : y = y₀ := by
        rcases mul_eq_zero.mp hfac with h' | h' <;> linear_combination h'
      subst hy

      have hneg : -(Affine.Point.some x y h) = Affine.Point.some x y h := by
        rw [Affine.Point.neg_some]
        congr 1
        simp only [Affine.negY]; linear_combination -hgy'
      rw [two_zsmul, ← neg_eq_iff_add_eq_zero, hneg]
    · exfalso
      rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ h hx] at ha
      exact Affine.Point.some_ne_zero _ ha

end HCoreReduction

open HCoreReduction in
theorem solution
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q : ℕ) [Fact q.Prime] [CharP κ q] {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (data : ModularPolynomialData ℓ) {j y : κ}
    (hj : j ∈ ssJSet q κ) (hy : y ∈ (fibrePoly data.Φ j).roots) :
    y ∈ ssJSet q κ := by
  have hℓP : ℓ.Prime := Fact.out
  have hqP : q.Prime := Fact.out
  have hℓK : (ℓ : κ) ≠ 0 := by
    intro h
    have hdvd : q ∣ ℓ := (CharP.cast_eq_zero_iff κ q ℓ).mp h
    exact hℓq ((Nat.prime_dvd_prime_iff_eq hqP hℓP).mp hdvd).symm
  have hcop : IsCoprime (ℓ : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hℓP hqP).mpr hℓq
  let W := WeierstrassCurve.ofJ j
  have hWj : W.j = j := WeierstrassCurve.ofJ_j j
  have hWss : ∀ P : W.toAffine.Point, (q : ℤ) • P = 0 → P = 0 := fun P hP =>
    hj W hWj P (by rwa [natCast_zsmul] at hP)
  have hy' : y ∈ (fibrePoly data.Φ W.j).roots := by rwa [hWj]
  intro W' _ hW'j P hP
  replace hP : (q : ℤ) • P = 0 := by rwa [natCast_zsmul]
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have h2 : (2 : κ) ≠ 0 := by exact_mod_cast hℓK
    obtain ⟨x₀, y₀, hQeq, hgy, hΔ, hjV⟩ :=
      ModularCurve.ModularPolynomialData.exists_veluQuotient2_j_eq_of_mem_roots_fibrePoly h2 data W hy'
    letI : (W.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    obtain ⟨φ, hφ⟩ := WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2 W h2 hQeq hgy hΔ
    have hsurj : Function.Surjective φ := by
      rw [hφ]; exact WeierstrassCurve.veluPointMap2_surjective_of_isAlgClosed W h2 hQeq hgy hΔ
    have hkerb : ∀ a, φ a = 0 → ((2 : ℕ) : ℤ) • a = 0 := fun a ha =>
      veluPointMap2_ker_two_torsion W h2 hQeq hgy hΔ a (by rw [← hφ]; exact ha)
    obtain ⟨ψ, hdual⟩ := AddMonoidHom.exists_isDualPair_of_surjective_of_ker_le φ hsurj _ hkerb
    have hVss := hdual.forall_q_zsmul_eq_zero_of_isCoprime q hcop hWss
    obtain ⟨e⟩ := nonempty_addEquiv_of_j_eq (W.veluQuotient2 x₀ y₀) W' (hjV.trans hW'j.symm)
    exact noTors_of_addEquiv e hVss P hP
  · obtain ⟨Q, hQ, hΔ, hjV⟩ :=
      ModularCurve.ModularPolynomialData.exists_veluQuotient_j_eq_of_mem_roots_fibrePoly hℓ2 hℓK data W hy'
    letI : (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2))).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    obtain ⟨φ, hker, hcoord⟩ := WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet W hℓP hℓ2 hℓK Q hQ
    have hsurj : Function.Surjective φ :=
      WeierstrassCurve.veluPointHom_surjective_of_isAlgClosed W hℓP hℓ2 hℓK Q hQ φ hcoord
    obtain ⟨ψ, hdual⟩ :=
      AddMonoidHom.exists_isDualPair_of_surjective_of_ker_le φ hsurj (ℓ : ℤ) (ker_bound hker hQ)
    have hVss := hdual.forall_q_zsmul_eq_zero_of_isCoprime q hcop hWss
    obtain ⟨e⟩ := nonempty_addEquiv_of_j_eq (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2))) W'
      (hjV.trans hW'j.symm)
    exact noTors_of_addEquiv e hVss P hP

end S_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly
end P2MW
export P2MW.S_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly (solution)
