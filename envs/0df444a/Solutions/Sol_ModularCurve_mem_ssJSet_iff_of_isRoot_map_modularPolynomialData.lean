-- Prove2me | solution 1 for ModularCurve.mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e466fa5c-d87e-5564-9025-604c1ae7104d

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_WeierstrassCurve_rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
import Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false

open Polynomial ModularCurve

universe u

namespace IsogSS

theorem eval_map_swapBivar {S : Type*} [CommRing S] (Φ : Polynomial (Polynomial ℤ)) (a b : S) :
    ((swapBivar Φ).map (eval₂RingHom (Int.castRingHom S) b)).eval a =
      (Φ.map (eval₂RingHom (Int.castRingHom S) a)).eval b := by

  let F₁ : Polynomial (Polynomial ℤ) →+* S :=
    (evalRingHom a).comp ((mapRingHom (eval₂RingHom (Int.castRingHom S) b)).comp swapBivar)
  let F₂ : Polynomial (Polynomial ℤ) →+* S :=
    (evalRingHom b).comp (mapRingHom (eval₂RingHom (Int.castRingHom S) a))
  have hF : F₁ = F₂ := by
    apply Polynomial.ringHom_ext
    · intro r
      change ((swapBivar (C r)).map (eval₂RingHom (Int.castRingHom S) b)).eval a =
        ((C r : Polynomial (Polynomial ℤ)).map (eval₂RingHom (Int.castRingHom S) a)).eval b
      have hr : swapBivar (C r) = swapInner r := by
        show Polynomial.eval₂ swapInner (C X) (C r) = swapInner r
        rw [Polynomial.eval₂_C]
      rw [hr, Polynomial.map_C, eval_C]
      change ((swapInner r).map (eval₂RingHom (Int.castRingHom S) b)).eval a = Polynomial.eval₂ (Int.castRingHom S) a r

      let G₁ : Polynomial ℤ →+* S := (evalRingHom a).comp ((mapRingHom (eval₂RingHom (Int.castRingHom S) b)).comp swapInner)
      let G₂ : Polynomial ℤ →+* S := eval₂RingHom (Int.castRingHom S) a
      have hG : G₁ = G₂ := by
        apply Polynomial.ringHom_ext
        · intro n
          change ((swapInner (C n)).map (eval₂RingHom (Int.castRingHom S) b)).eval a = Polynomial.eval₂ (Int.castRingHom S) a (C n)
          have : swapInner (C n) = C (C n) := by
            show Polynomial.aeval (R := ℤ) (X : Polynomial (Polynomial ℤ)) (C n) = C (C n)
            rw [Polynomial.aeval_C]
            rfl
          rw [this, Polynomial.map_C, eval_C, Polynomial.eval₂_C]
          change Polynomial.eval₂ (Int.castRingHom S) b (C n) = _
          rw [Polynomial.eval₂_C]
        · change ((swapInner X).map (eval₂RingHom (Int.castRingHom S) b)).eval a = Polynomial.eval₂ (Int.castRingHom S) a X
          have : swapInner (X : Polynomial ℤ) = (X : Polynomial (Polynomial ℤ)) := Polynomial.aeval_X _
          rw [this, Polynomial.map_X, eval_X, Polynomial.eval₂_X]
      exact congrArg (fun G : Polynomial ℤ →+* S => G r) hG
    · change ((swapBivar X).map (eval₂RingHom (Int.castRingHom S) b)).eval a =
        ((X : Polynomial (Polynomial ℤ)).map (eval₂RingHom (Int.castRingHom S) a)).eval b
      rw [swapBivar_X, Polynomial.map_C, eval_C, Polynomial.map_X, eval_X]
      change Polynomial.eval₂ (Int.castRingHom S) b X = b
      rw [Polynomial.eval₂_X]
  exact congrArg (fun F : Polynomial (Polynomial ℤ) →+* S => F Φ) hF

theorem cyclicQuotientCurve_prime {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    (H : AddSubgroup E.toAffine.Point) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    E.cyclicQuotientCurve H ℓ = E.stepCurve H ℓ := by
  rw [WeierstrassCurve.cyclicQuotientCurve_def, WeierstrassCurve.cqjIterate_eq_of_two_le E H hℓ.two_le,
    Nat.Prime.minFac_eq hℓ, Nat.div_self hℓ.pos, WeierstrassCurve.cqjIterate_one]

theorem j_eq_c₄_div {L : Type u} [Field L] (V : WeierstrassCurve L) [V.IsElliptic] :
    V.j = V.c₄ ^ 3 / V.Δ := by
  rw [WeierstrassCurve.j, div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']

theorem eq_zero_of_nsmul_eq_zero_of_nsmul_eq_zero {G : Type*} [AddCommGroup G] {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hne : ℓ ≠ p) {P : G} (h₁ : p • P = 0) (h₂ : ℓ • P = 0) : P = 0 := by
  have h1 : addOrderOf P ∣ p := addOrderOf_dvd_of_nsmul_eq_zero h₁
  have h2 : addOrderOf P ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero h₂
  have hcop : Nat.Coprime p ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hne)
  have : addOrderOf P ∣ 1 := by
    rw [← hcop]
    exact Nat.dvd_gcd h1 h2
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem torsionFree_of_velu {Ω : Type u} [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω]
    (E : WeierstrassCurve Ω) [E.IsElliptic] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓΩ : (ℓ : Ω) ≠ 0)
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = ℓ) {p : ℕ} (hp : p.Prime) (hne : ℓ ≠ p)
    (h : ∀ P' : (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).toAffine.Point, p • P' = 0 → P' = 0) :
    ∀ P : E.toAffine.Point, p • P = 0 → P = 0 := by
  obtain ⟨φ, hker, -⟩ := WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed E hℓ hℓ2 hℓΩ Q hQ
  intro P hP
  have h1 : φ P = 0 := h _ (by rw [← map_nsmul, hP, map_zero])
  have h2 : P ∈ AddSubgroup.zmultiples Q := by rw [← hker]; exact h1
  have h3 : ℓ • P = 0 := by
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
    rw [← natCast_zsmul, smul_comm, natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero, smul_zero]
  exact eq_zero_of_nsmul_eq_zero_of_nsmul_eq_zero hp hℓ hne hP h3

theorem torsionFree_of_velu2 {Ω : Type u} [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω] (h2 : (2 : Ω) ≠ 0)
    (E : WeierstrassCurve Ω) [E.IsElliptic] {x₀ y₀ : Ω} (hQ : E.toAffine.Equation x₀ y₀) (hgy : E.veluGy x₀ y₀ = 0)
    (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hne : 2 ≠ p)
    (h : ∀ P' : (E.veluQuotient2 x₀ y₀).toAffine.Point, p • P' = 0 → P' = 0) :
    ∀ P : E.toAffine.Point, p • P = 0 → P = 0 := by
  obtain ⟨π, -, -, ⟨π', -, hππ, -⟩, -⟩ :=
    WeierstrassCurve.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul h2 E hQ hgy hΔ
  intro P hP
  have h1 : π P = 0 := h _ (by rw [← map_nsmul, hP, map_zero])
  have h3 : 2 • P = 0 := by
    have e1 := DFunLike.congr_fun hππ P
    change π' (π P) = (2 • AddMonoidHom.id E.toAffine.Point) P at e1
    have h0 : π' (π P) = 0 := by rw [h1]; exact map_zero π'
    rw [h0, two_nsmul, AddMonoidHom.add_apply, AddMonoidHom.id_apply] at e1
    rw [two_nsmul]; exact e1.symm
  exact eq_zero_of_nsmul_eq_zero_of_nsmul_eq_zero hp Nat.prime_two hne hP h3

theorem two_torsion_veluGy {Ω : Type u} [Field Ω] [DecidableEq Ω] (E : WeierstrassCurve Ω)
    {x₀ y₀ : Ω} (hns : E.toAffine.Nonsingular x₀ y₀) (h2 : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : E.toAffine.Point) = 0) :
    E.veluGy x₀ y₀ = 0 := by
  have hneg : -(WeierstrassCurve.Affine.Point.some x₀ y₀ hns : E.toAffine.Point) = .some x₀ y₀ hns := by
    rw [two_nsmul] at h2
    exact (neg_eq_of_add_eq_zero_left h2)
  rw [WeierstrassCurve.Affine.Point.neg_some] at hneg
  have hy : E.toAffine.negY x₀ y₀ = y₀ := (WeierstrassCurve.Affine.Point.some.inj hneg).2
  rw [WeierstrassCurve.veluGy]
  rw [WeierstrassCurve.Affine.negY] at hy
  linear_combination hy

theorem exists_model_cyclicQuotient {Ω : Type u} [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω]
    (E : WeierstrassCurve Ω) [E.IsElliptic] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΩ : (ℓ : Ω) ≠ 0)
    (H : AddSubgroup E.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = ℓ)
    {p : ℕ} (hp : p.Prime) (hne : ℓ ≠ p) :
    ∃ (W' : WeierstrassCurve Ω) (_ : W'.IsElliptic), W'.j = E.cyclicQuotientJ H ℓ ∧
      ((∀ P' : W'.toAffine.Point, p • P' = 0 → P' = 0) → ∀ P : E.toAffine.Point, p • P = 0 → P = 0) := by
  haveI : IsAddCyclic H := hcyc
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_ofOrder_eq_natCard (α := H)
  rw [hcard] at hg
  set Q : E.toAffine.Point := (g : E.toAffine.Point) with hQdef
  have hQH : Q ∈ H := g.2
  have hQ : addOrderOf Q = ℓ := by rw [hQdef, AddSubgroup.addOrderOf_coe]; exact hg
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2

    have hQ0 : Q ≠ 0 := by
      intro h0; rw [h0, addOrderOf_zero] at hQ; exact absurd hQ (by norm_num)
    obtain ⟨x₀, y₀, hns, hQeq⟩ : ∃ (x₀ y₀ : Ω) (hns : E.toAffine.Nonsingular x₀ y₀), Q = .some x₀ y₀ hns := by
      rcases Q with _ | ⟨x₀, y₀, hns⟩
      · exact absurd rfl hQ0
      · exact ⟨x₀, y₀, hns, rfl⟩
    have h2Q : (2 : ℕ) • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
    have hgy : E.veluGy x₀ y₀ = 0 := two_torsion_veluGy E hns (by rw [← hQeq]; exact h2Q)
    haveI hell : (E.veluQuotient2 x₀ y₀).IsElliptic := WeierstrassCurve.isElliptic_veluQuotient2_of_isElliptic hns.1 hgy
    have hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0 := (E.veluQuotient2 x₀ y₀).Δ'.ne_zero
    have h2Ω : (2 : Ω) ≠ 0 := by exact_mod_cast hℓΩ
    obtain ⟨π, hπ, -, -, -⟩ :=
      WeierstrassCurve.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul h2Ω E hns.1 hgy hΔ
    have hstep := WeierstrassCurve.stepCurve_stepSubgroup_two_eq E h2Ω H hns (hQeq ▸ hQH) hgy hΔ π hπ
    have hcurve : E.stepCurve H 2 = E.veluQuotient2 x₀ y₀ := congrArg Sigma.fst hstep
    refine ⟨E.veluQuotient2 x₀ y₀, hell, ?_, fun h => torsionFree_of_velu2 h2Ω E hns.1 hgy hΔ hp hne h⟩
    rw [j_eq_c₄_div, WeierstrassCurve.cyclicQuotientJ_def, cyclicQuotientCurve_prime E H Nat.prime_two, hcurve]
  · obtain ⟨φ, hker, hφ⟩ := WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed E hℓ hℓ2 hℓΩ Q hQ
    have hodd : ℓ = 2 * (ℓ / 2) + 1 := by
      have := hℓ.eq_two_or_odd'.resolve_left hℓ2
      obtain ⟨k, hk⟩ := this
      omega
    have hΔ : (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).Δ ≠ 0 :=
      WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq E (ℓ / 2) Q (by rw [hQ]; exact hodd)
    haveI hell : (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    have hstep := WeierstrassCurve.stepCurve_stepSubgroup_eq_of_prime_ne_two E hℓ hℓ2 H Q hQH hQ φ hker hφ
    have hcurve : E.stepCurve H ℓ = E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)) := congrArg Sigma.fst hstep
    refine ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), hell, ?_,
      fun h => torsionFree_of_velu E hℓ hℓ2 hℓΩ Q hQ hp hne h⟩
    rw [j_eq_c₄_div, WeierstrassCurve.cyclicQuotientJ_def, cyclicQuotientCurve_prime E H hℓ, hcurve]

end IsogSS

theorem solution
    (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (data : ModularCurve.ModularPolynomialData ℓ)
    (Ω : Type u) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (x x' : Ω)
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x)).IsRoot x') :
    x ∈ ModularCurve.ssJSet p Ω ↔ x' ∈ ModularCurve.ssJSet p Ω := by
  classical
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hℓΩ : (ℓ : Ω) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff Ω p] at h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm

  have key : ∀ a b : Ω, (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) a)).IsRoot b →
      b ∈ ModularCurve.ssJSet p Ω → a ∈ ModularCurve.ssJSet p Ω := by
    intro a b hab hb
    rw [ModularCurve.mem_ssJSet_iff]
    intro E _ hEj P hP
    have hne : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) E.j) ≠ 0 := (data.monic.map _).ne_zero
    have hpos : 0 < (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) E.j)).rootMultiplicity b := by
      rw [Polynomial.rootMultiplicity_pos hne, hEj]; exact hab
    rw [WeierstrassCurve.rootMultiplicity_map_modularPolynomial_j_eq_natCard_cyclicQuotientJ_eq ℓ data Ω hℓΩ E b] at hpos
    obtain ⟨⟨H, ⟨hcyc, hcard⟩, hHj⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    obtain ⟨W', hW', hj', htrans⟩ := IsogSS.exists_model_cyclicQuotient E hℓ hℓΩ H hcyc hcard hp hℓp
    haveI := hW'
    apply htrans _ P hP
    rw [hHj] at hj'
    exact (ModularCurve.mem_ssJSet_iff.mp hb) W' hj'
  constructor
  · intro hx
    apply key x' x _ hx
    have hsym := ModularCurve.swapBivar_eq_of_evalSymm (ModularCurve.ModularPolynomialData.evalSymm_of_prime ℓ data)
    rw [Polynomial.IsRoot.def, ← hsym, IsogSS.eval_map_swapBivar]
    exact hroot
  · intro hx'
    exact key x x' hroot hx'

end S_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
end P2MW
export P2MW.S_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData (solution)
