-- Prove2me | solution 1 for ModularCurve.exists_natCast_mul_inv_nodeCoord_mem_integers_ord_residue_eq_one_inftyChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5842b7b8-518e-5f4d-a77c-2581ab716b48

import Mathlib
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_natCast_mul_inv_nodeCoord_mem_integers_ord_residue_eq_one_inftyChart
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_natCast_mul_inv_nodeCoord_mem_integers_ord_residue_eq_one_inftyChart.ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_natCast_mul_inv_nodeCoord_mem_integers_ord_residue_eq_one_inftyChart.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "nonempty_modularPolynomialData qExpand jq evalAtJ evalAtJ_X ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full ModularPolynomialData.eval_eq_zero kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence eval_kroneckerRemainder_ne_zero_of_mem_ssJSet modularFunctionFieldBar coeffEmb coeffEmb_mem_laurentBaseChange ssJSet"
namespace Ws23
p2m_open "ModularCurve"

open IsLocalRing

theorem exists_zpow_mem_isUnit {L : Type*} [Field L] {A : ValuationSubring L} {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) (n : ℤ) : ∃ h : a ^ n ∈ A, IsUnit (⟨a ^ n, h⟩ : A) := by
  have hv : A.valuation a = 1 := (A.valuation_eq_one_iff ⟨a, ha⟩).mp hu
  have hvn : A.valuation (a ^ n) = 1 := by rw [map_zpow₀, hv, one_zpow]
  have hmem : a ^ n ∈ A := (A.valuation_le_one_iff _).mp hvn.le
  exact ⟨hmem, (A.valuation_eq_one_iff ⟨a ^ n, hmem⟩).mpr hvn⟩

theorem inv_mem_of_isUnit {L : Type*} [Field L] {A : ValuationSubring L} {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) : a⁻¹ ∈ A := by
  obtain ⟨h, -⟩ := exists_zpow_mem_isUnit ha hu (-1)
  simpa only [zpow_neg, zpow_one] using h

theorem map_eval₂_eval₂RingHom_intCast {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T)
    (R : Polynomial (Polynomial ℤ)) (x y : S) :
    g (R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y)
      = R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom T) (g x)) (g y) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.eval₂_X]

theorem mapRingHom_intCast_eq {S : Type*} [CommRing S] :
    Polynomial.mapRingHom (Int.castRingHom S)
      = Polynomial.eval₂RingHom (Int.castRingHom (Polynomial S)) Polynomial.X := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  rw [Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem eval₂_of_kroneckerForm {S : Type*} [CommRing S] (q : ℕ) (Φ R : Polynomial (Polynomial ℤ))
    (hR : Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
      + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (x y : S) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y
      = (x ^ q - y) * (x - y ^ q) + (q : S) * R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y := by
  subst hR
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom]
  simp only [map_natCast, eq_intCast, Int.cast_natCast]

theorem aeval_ne_zero_of_ord_eq_rootMultiplicity {k Fbar : Type*} [Field k] [IsAlgClosed k] [Field Fbar]
    [Algebra k Fbar] (X : Fbar) (xpl : k → Place k Fbar)
    (hord_poly : ∀ (c : k) (P : Polynomial k), (xpl c).ord (Polynomial.aeval X P) = (P.rootMultiplicity c : ℤ))
    {P : Polynomial k} (hP : P ≠ 0) : Polynomial.aeval X P ≠ 0 := by
  intro h0
  by_cases hdeg : P.degree = 0
  · rw [Polynomial.eq_C_of_degree_eq_zero hdeg, Polynomial.aeval_C, map_eq_zero] at h0
    apply hP
    rw [Polynomial.eq_C_of_degree_eq_zero hdeg, h0, map_zero]
  · obtain ⟨c, hc⟩ := IsAlgClosed.exists_root P hdeg
    have h1 := hord_poly c P
    rw [h0, Place.ord_zero] at h1
    have h2 : 0 < P.rootMultiplicity c := (Polynomial.rootMultiplicity_pos hP).mpr hc
    omega

theorem derivative_X_sub_X_pow_sq (k : Type*) [CommRing k] (p : ℕ) [CharP k p] :
    Polynomial.derivative (Polynomial.X - Polynomial.X ^ (p ^ 2) : Polynomial k) = 1 := by
  rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_X_pow]
  have : ((p ^ 2 : ℕ) : k) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero k p, zero_pow two_ne_zero]
  rw [this, map_zero, zero_mul, sub_zero]

theorem X_sub_X_pow_sq_ne_zero (k : Type*) [CommRing k] [Nontrivial k] (p : ℕ) [Fact p.Prime] :
    (Polynomial.X - Polynomial.X ^ (p ^ 2) : Polynomial k) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h
  have h' : (Polynomial.X : Polynomial k) = Polynomial.X ^ (p ^ 2) := sub_eq_zero.mp h
  have hdeg := congrArg Polynomial.natDegree h'
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at hdeg
  rcases pow_eq_one_iff.mp hdeg.symm with h1 | h1
  · exact hp.one_lt.ne' h1
  · exact two_ne_zero h1

theorem rootMultiplicity_X_sub_X_pow_sq_eq_one (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (b : k) (hb : b ^ (p ^ 2) = b) :
    (Polynomial.X - Polynomial.X ^ (p ^ 2) : Polynomial k).rootMultiplicity b = 1 := by
  set Q : Polynomial k := Polynomial.X - Polynomial.X ^ (p ^ 2) with hQ
  have hQ0 : Q ≠ 0 := X_sub_X_pow_sq_ne_zero k p
  have hroot : Q.IsRoot b := by
    simp only [hQ, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow, hb,
      sub_self]
  have hge : 1 ≤ Q.rootMultiplicity b := (Polynomial.rootMultiplicity_pos hQ0).mpr hroot
  have hle : Q.rootMultiplicity b ≤ 1 := by
    by_contra hlt
    have hlt' : 1 < Q.rootMultiplicity b := not_le.mp hlt
    have hder := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt'
    rw [Function.iterate_one, hQ, derivative_X_sub_X_pow_sq k p] at hder
    simp at hder
  omega

theorem exists_kroneckerRemainder (q : ℕ) [Fact q.Prime] (data : ModularPolynomialData q) :
    ∃ R : Polynomial (Polynomial ℤ),
      data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
        + Polynomial.C (Polynomial.C (q : ℤ)) * R := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hKr : KroneckerCongruence q data := kroneckerCongruence q data
  have hdvd : Polynomial.C (Polynomial.C (q : ℤ)) ∣
      data.Φ - (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h := congrArg (fun S : Polynomial (Polynomial (ZMod q)) => (S.coeff n).coeff m) hKr
    have hprod : reduceModBivar q ((Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q))
        = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
      simp only [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]
    rw [← hprod] at h
    simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, eq_intCast] at h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.coeff_sub, Polynomial.coeff_sub, Int.cast_sub, sub_eq_zero]
    exact h
  obtain ⟨R, hR⟩ := hdvd
  exact ⟨R, by rw [← hR]; ring⟩

theorem eval₂_modularPolynomial_eq_zero (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar p)) (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : ↥(modularFunctionFieldBar p)))
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : ↥(modularFunctionFieldBar p)) = 0 := by
  have h0 := data.eval_eq_zero
  have hev : (evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ)
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [hev] at h0
  have h1 := congrArg (coeffEmb (AlgebraicClosure ℚ)) h0
  rw [map_zero, map_eval₂_eval₂RingHom_intCast] at h1
  apply Subtype.val_injective
  have h2 := map_eval₂_eval₂RingHom_intCast ((modularFunctionFieldBar p).val.toRingHom) data.Φ (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : ↥(modularFunctionFieldBar p)) (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : ↥(modularFunctionFieldBar p))
  exact h2.trans h1

end ModularCurve.Ws23

open ModularCurve.Ws23 in

theorem solution
    (p : ℕ) [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (C : ComponentChart A ↥(modularFunctionFieldBar p) Fbar)
    (X : Fbar) (xpl : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbar)
    (hord_poly : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpl c).ord (Polynomial.aeval X P) = (P.rootMultiplicity c : ℤ))
    (hjF : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : ↥(modularFunctionFieldBar p)) ∈ C.integers)
    (hjpF : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : ↥(modularFunctionFieldBar p)) ∈ C.integers)
    (hres_j : C.residue ⟨_, hjF⟩ = X) (hres_jp : C.residue ⟨_, hjpF⟩ = X ^ p)
    (hp5 : 5 ≤ p) (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) (p : AlgebraicClosure ℚ)
          * ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : ↥(modularFunctionFieldBar p))
              - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : ↥(modularFunctionFieldBar p)) ^ p)⁻¹ ∈ C.integers,
      (xpl a).ord (C.residue ⟨_, h⟩) = 1 := by
  classical
  have hp : p.Prime := Fact.out
  set jF : ↥(modularFunctionFieldBar p) := (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : ↥(modularFunctionFieldBar p)) with hjF_def
  set jpF : ↥(modularFunctionFieldBar p) := (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : ↥(modularFunctionFieldBar p)) with hjpF_def

  obtain ⟨data⟩ := nonempty_modularPolynomialData p
  obtain ⟨R, hR⟩ := exists_kroneckerRemainder p data
  have hRa := eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hp5 data R hR a ha h0 h1728

  set H : ↥(modularFunctionFieldBar p) := jF - jpF ^ p with hH
  set G : ↥(modularFunctionFieldBar p) := jpF - jF ^ p with hG
  set RF : ↥(modularFunctionFieldBar p) :=
    R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar p)) jF) jpF with hRF
  set Rint : ↥C.integers :=
    R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥C.integers) ⟨jF, hjF⟩) ⟨jpF, hjpF⟩ with hRint
  set P : Polynomial (IsLocalRing.ResidueField ↥A) := (R.map (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).eval (Polynomial.X ^ p) with hP

  have hK : (jF ^ p - jpF) * (jF - jpF ^ p) + (p : ↥(modularFunctionFieldBar p)) * RF = 0 := by
    rw [hRF, ← eval₂_of_kroneckerForm p data.Φ R hR jF jpF]
    exact eval₂_modularPolynomial_eq_zero p data
  have hGH : G * H = (p : ↥(modularFunctionFieldBar p)) * RF := by
    rw [hG, hH]
    linear_combination (-1 : ↥(modularFunctionFieldBar p)) * hK

  have hRint_coe : (Rint : ↥(modularFunctionFieldBar p)) = RF := by
    rw [hRint, hRF]
    exact map_eval₂_eval₂RingHom_intCast (C.integers.subtype) R ⟨jF, hjF⟩ ⟨jpF, hjpF⟩
  have hP_eq : P = R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (Polynomial (IsLocalRing.ResidueField ↥A))) Polynomial.X)
      (Polynomial.X ^ p) := by
    rw [hP, Polynomial.eval_map, mapRingHom_intCast_eq]
  have haevalP : Polynomial.aeval X P
      = R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom Fbar) X) (X ^ p) := by
    rw [hP_eq]
    have h := map_eval₂_eval₂RingHom_intCast ((Polynomial.aeval X).toRingHom) R
      (Polynomial.X : Polynomial (IsLocalRing.ResidueField ↥A)) (Polynomial.X ^ p)
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.coe_coe, map_pow,
      Polynomial.aeval_X] using h
  have hresP : C.residue Rint = Polynomial.aeval X P := by
    rw [haevalP, hRint]
    have h := map_eval₂_eval₂RingHom_intCast C.residue R ⟨jF, hjF⟩ ⟨jpF, hjpF⟩
    rw [hres_j, hres_jp] at h
    exact h

  have hRa' : R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)) a) (a ^ p) ≠ 0 := by
    have h := map_eval₂_eval₂RingHom_intCast (Polynomial.evalRingHom a) R
      (Polynomial.X : Polynomial (IsLocalRing.ResidueField ↥A)) (Polynomial.C (a ^ p))
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_C] at h
    rw [← h, ← mapRingHom_intCast_eq, ← Polynomial.eval_map]
    exact hRa
  have hPa : ¬ P.IsRoot a := by
    intro hroot
    apply hRa'
    have h := map_eval₂_eval₂RingHom_intCast (Polynomial.evalRingHom a) R
      (Polynomial.X : Polynomial (IsLocalRing.ResidueField ↥A)) (Polynomial.X ^ p)
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_X] at h
    rw [← h, ← hP_eq]
    exact hroot
  have hP0 : P ≠ 0 := fun h => hPa (by rw [h, Polynomial.IsRoot, Polynomial.eval_zero])
  have hXP : Polynomial.aeval X P ≠ 0 := aeval_ne_zero_of_ord_eq_rootMultiplicity X xpl hord_poly hP0

  set Q : Polynomial (IsLocalRing.ResidueField ↥A) := Polynomial.X - Polynomial.X ^ (p ^ 2) with hQ
  have hQ0 : Q ≠ 0 := X_sub_X_pow_sq_ne_zero (IsLocalRing.ResidueField ↥A) p
  have hXQ : Polynomial.aeval X Q ≠ 0 := aeval_ne_zero_of_ord_eq_rootMultiplicity X xpl hord_poly hQ0
  have hHmem : H ∈ C.integers := sub_mem hjF (pow_mem hjpF p)
  have hresH : C.residue ⟨H, hHmem⟩ = Polynomial.aeval X Q := by
    have hsplit : (⟨H, hHmem⟩ : ↥C.integers) = ⟨jF, hjF⟩ - ⟨jpF, hjpF⟩ ^ p := rfl
    rw [hsplit, map_sub, map_pow, hres_j, hres_jp, ← pow_mul, ← sq, hQ]
    simp only [map_sub, map_pow, Polynomial.aeval_X]

  have hRunit : IsUnit Rint := by
    by_contra hnu
    apply hXP
    rw [← hresP, ← RingHom.mem_ker, C.ker_residue, IsLocalRing.mem_maximalIdeal]
    exact hnu
  have hRFmem : RF ∈ C.integers := hRint_coe ▸ Rint.2
  have hRint_eq : (⟨RF, hRFmem⟩ : ↥C.integers) = Rint := Subtype.ext hRint_coe.symm
  have hRunit' : IsUnit (⟨RF, hRFmem⟩ : ↥C.integers) := by rw [hRint_eq]; exact hRunit
  have hRinv : RF⁻¹ ∈ C.integers := inv_mem_of_isUnit hRFmem hRunit'
  have hRF0 : RF ≠ 0 := by
    intro h
    apply hXP
    rw [← hresP, ← hRint_eq]
    have h' : (⟨RF, hRFmem⟩ : ↥C.integers) = 0 := Subtype.ext h
    rw [h', map_zero]
  have hH0 : H ≠ 0 := by
    intro h
    apply hXQ
    rw [← hresH]
    have h' : (⟨H, hHmem⟩ : ↥C.integers) = 0 := Subtype.ext h
    rw [h', map_zero]
  have hpQ : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpF : ((p : ℕ) : ↥(modularFunctionFieldBar p)) ≠ 0 := by
    rw [← map_natCast (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))]
    exact (map_ne_zero _).mpr hpQ
  have hG0 : G ≠ 0 := by
    intro h
    rw [h, zero_mul] at hGH
    exact (mul_ne_zero hpF hRF0) hGH.symm

  have h1 : H = (p : ↥(modularFunctionFieldBar p)) * RF * G⁻¹ := by
    rw [← hGH, mul_comm G H, mul_inv_cancel_right₀ hG0]
  have helt : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) (p : AlgebraicClosure ℚ) * G⁻¹
      = H * RF⁻¹ := by
    rw [map_natCast, h1, mul_right_comm ((p : ↥(modularFunctionFieldBar p)) * RF) G⁻¹ RF⁻¹,
      mul_inv_cancel_right₀ hRF0]
  have hmem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) (p : AlgebraicClosure ℚ) * G⁻¹
      ∈ C.integers := by
    rw [helt]
    exact mul_mem hHmem hRinv
  refine ⟨hmem, ?_⟩

  have hsplit2 : (⟨_, hmem⟩ : ↥C.integers) = ⟨H, hHmem⟩ * ⟨RF⁻¹, hRinv⟩ := Subtype.ext helt
  have hresinv : C.residue ⟨RF⁻¹, hRinv⟩ = (C.residue ⟨RF, hRFmem⟩)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, ← map_one C.residue]
    congr 1
    exact Subtype.ext (mul_inv_cancel₀ hRF0)
  have hresRF : C.residue ⟨RF, hRFmem⟩ = Polynomial.aeval X P := by rw [hRint_eq]; exact hresP
  rw [hsplit2, map_mul, hresH, hresinv, hresRF, Place.ord_mul _ hXQ (inv_ne_zero hXP), Place.ord_inv,
    hord_poly, hord_poly, hQ, rootMultiplicity_X_sub_X_pow_sq_eq_one (IsLocalRing.ResidueField ↥A) p a ha2,
    Polynomial.rootMultiplicity_eq_zero hPa]
  norm_num

end S_ModularCurve_exists_natCast_mul_inv_nodeCoord_mem_integers_ord_residue_eq_one_inftyChart
end P2MW
export P2MW.S_ModularCurve_exists_natCast_mul_inv_nodeCoord_mem_integers_ord_residue_eq_one_inftyChart (solution)
