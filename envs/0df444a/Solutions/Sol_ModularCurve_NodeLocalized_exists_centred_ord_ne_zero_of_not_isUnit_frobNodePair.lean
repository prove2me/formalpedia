-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1002df77-919d-532e-a6f5-6e4ab205958e

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_exists_place_centred_node_of_height_one_of_natCast_notMem
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_exists_heightOne_mem_of_mul_eq_of_not_isUnit_frobNodePair
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_mem_jIntegralClosure_of_not_isUnit_frobNodePair
import Theorems.Thm_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_ne_zero_of_ne_1728
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

noncomputable section

open Polynomial in

private scoped instance instIsAlgClosedResidueField_reMint {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)
  have hf_lifts : f ∈ lifts (IsLocalRing.residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => IsLocalRing.residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0
    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]; exact hg_nat
    exact hf_irr.not_isUnit (by rw [(hf_monic.natDegree_eq_zero).mp hf_deg]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg
  have hα_int : IsIntegral A α := ⟨g, hg_monic, by rwa [IsRoot.def, eval_map] at hα⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      rw [show algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α from by
        rw [← ha, eval_map, eval₂_hom]]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  rw [show f.eval (IsLocalRing.residue A a) = IsLocalRing.residue A (g.eval a) from by
    rw [← hg_map, eval_map, eval₂_hom], hga, map_zero]

private theorem withZero_eq_one_of_log_eq_zero
    (x : WithZero (Multiplicative ℤ)) (hne : x ≠ 0) (hlog : WithZero.log x = 0) : x = 1 := by
  obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.mp hne
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero _) from rfl,
    WithZero.coe_inj]
  have hta : Multiplicative.toAdd m = (0 : ℤ) := hlog
  exact Multiplicative.toAdd.injective (by rw [hta]; rfl)

private theorem inv_mem_of_isUnit {F : Type*} [Field F] (V : ValuationSubring F)
    (f : F) (hfW : f ∈ V) (hu : IsUnit (⟨f, hfW⟩ : V)) : f⁻¹ ∈ V := by
  obtain ⟨u, hueq⟩ := hu
  have h1 : ((↑u⁻¹ : ↥V) : F) = f⁻¹ := by
    have h2 : ((↑u : ↥V) : F) = f := by rw [hueq]
    have h3 : ((↑u : ↥V) : F) * ((↑u⁻¹ : ↥V) : F) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
    rw [h2] at h3
    exact eq_inv_of_mul_eq_one_right h3
  exact h1 ▸ (↑u⁻¹ : ↥V).2

private theorem eq_two_or_eq_three_of_prime_of_lt_five {q : ℕ} (hp : q.Prime) (hq : q < 5) :
    q = 2 ∨ q = 3 := by
  have h2 := hp.two_le
  interval_cases q
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hp (by norm_num)

private theorem mem_range_red_of_pow_q_sq_eq_self {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha2 : a ^ (q ^ 2) = a) : a ∈ Set.range red := by
  classical
  have hH : ∀ c ∈ IsLocalRing.maximalIdeal (↥A), red c = 0 := fun c hc => (hker c).mpr hc
  haveI h2s : (IsLocalRing.maximalIdeal (↥A)).IsTwoSided := inferInstance
  let φ : IsLocalRing.ResidueField ↥A →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥A) red hH
  have hred : ∀ c : ↥A, red c = φ (IsLocalRing.residue A c) := fun c =>
    (Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal ↥A) red hH).symm
  letI : Algebra (IsLocalRing.ResidueField ↥A) k := φ.toAlgebra
  haveI hRFac : IsAlgClosed (IsLocalRing.ResidueField ↥A) := instIsAlgClosedResidueField_reMint A
  have halg : IsIntegral (IsLocalRing.ResidueField ↥A) a := by
    refine ⟨Polynomial.X ^ (q^2) - Polynomial.X, ?_, ?_⟩
    · refine (Polynomial.monic_X_pow (q^2)).sub_of_left ?_
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).two_le
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
      exact sub_eq_zero_of_eq ha2
  have hdeg : (minpoly (IsLocalRing.ResidueField ↥A) a).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible halg)
  obtain ⟨b, hb⟩ := minpoly.mem_range_of_degree_eq_one (IsLocalRing.ResidueField ↥A) a hdeg
  obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (R := ↥A) b
  exact ⟨c, by rw [hred c, hc]; exact hb⟩

private theorem exists_mul_eq_one_of_redRestrict_ne_zero
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) (hc : redRestrict red K c ≠ 0) :
    ∃ d : ↥(coeffSubring A K), c * d = 1 := by
  let cA : A := Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) c
  have hcA : cA ∉ IsLocalRing.maximalIdeal A := fun h => hc ((hker cA).mpr h)
  obtain ⟨b, hb⟩ := (IsLocalRing.notMem_maximalIdeal.mp hcA).exists_right_inv
  have hb' : (c : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hb
  have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hb'; exact zero_ne_one hb'
  have hbinv : (b : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hb'
  have hbK : (b : AlgebraicClosure ℚ) ∈ K.toSubalgebra.toSubring := by
    rw [hbinv]
    exact K.inv_mem (Subring.mem_inf.mp c.2).2
  refine ⟨⟨(b : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨b.2, hbK⟩⟩, Subtype.ext ?_⟩
  exact hb'

private theorem exists_uniformizer_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with hEq | hDVR
  · exfalso
    have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hinv : (q : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [hEq]
      show (q : AlgebraicClosure ℚ)⁻¹ ∈ K
      exact inv_mem (natCast_mem K q)
    have hcoe : (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) :=
      map_natCast (coeffSubring A K).subtype q
    have hone : ((q : ℕ) : ↥(coeffSubring A K)) * ⟨_, hinv⟩ = 1 := by
      apply Subtype.ext
      show (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) * (q : AlgebraicClosure ℚ)⁻¹ = 1
      rw [hcoe, mul_inv_cancel₀ hq0]
    have h := congrArg (redRestrict red K) hone
    rw [map_mul, map_natCast, CharP.cast_eq_zero k q, zero_mul, map_one] at h
    exact zero_ne_one h
  · haveI := hDVR
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
    have hmax : IsLocalRing.maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    refine ⟨ϖ, fun c => ⟨fun hc0 => ?_, ?_⟩⟩
    · have hcm : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨d, hd⟩ := hu.exists_right_inv
        have h := congrArg (redRestrict red K) hd
        rw [map_mul, hc0, zero_mul, map_one] at h
        exact zero_ne_one h
      rw [hmax, Ideal.mem_span_singleton'] at hcm
      obtain ⟨d, hd⟩ := hcm
      exact ⟨d, by rw [← hd, mul_comm]⟩
    · rintro ⟨d, rfl⟩
      rw [map_mul]
      suffices hϖ0 : redRestrict red K ϖ = 0 by rw [hϖ0, zero_mul]
      by_contra hne
      obtain ⟨e, he⟩ := exists_mul_eq_one_of_redRestrict_ne_zero red hker K ϖ hne
      exact hϖ.not_isUnit (IsUnit.of_mul_eq_one e he)

private theorem core
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (hq : 5 ≤ q) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K) :
    False := by
  have hfR : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) :=
    ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_ne_zero_of_ne_1728
      red hker hq a ha ha2 h0 h1728 f h₁ h₁F h₁u h₂ h₂F h₂u hford K hx hfK
  have hMC :=
    exists_mul_eq_mem_jIntegralClosure_of_not_isUnit_frobNodePair red hker a ha ha2 h0 h1728
      f h₁ h₁F h₁u h₂ h₂F h₂u hmem hnu K hfK hfR
  obtain ⟨p, s, s₀, hs_eq, hps0, hfsp⟩ := hMC

  obtain ⟨x, hxa⟩ := hx
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer_coeffSubring red hker K
  have hpBlock :
      ∃ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) (_ : 𝔭.IsPrime), 𝔭.height = 1 ∧
        ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 ∧ p ∈ 𝔭 ∧
        (∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K),
          pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0 →
            ∀ ht : modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K,
              (⟨_, ht⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :=
    exists_heightOne_mem_of_mul_eq_of_not_isUnit_frobNodePair red hker a ha ha2 h0 h1728 f h₁ h₁F h₁u h₂ h₂u
      hmem hnu K hfK x hxa ϖ hϖ p s s₀ hs_eq hps0 hfsp
  obtain ⟨𝔭, hpr, h𝔭1, hq𝔭, hp𝔭, h𝔭S⟩ := hpBlock
  haveI := hpr
  have hs_eq' : s = ⟨modularEval (1 * q) (coeffSubring A K) s₀, hs_eq ▸ s.2⟩ := Subtype.ext hs_eq
  have hs𝔭 : s ∉ 𝔭 := hs_eq' ▸ h𝔭S s₀ hps0 (hs_eq ▸ s.2)
  have h653 :=
    ModularCurve.exists_place_centred_node_of_height_one_of_natCast_notMem red a K 𝔭 h𝔭1 hq𝔭 h𝔭S
  obtain ⟨W, hWc, hWiff⟩ := h653
  have hord : W.ord f = 0 := hford W hWc

  have hf0 : (f : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro hf0; apply h₁u
    have hz : (⟨_, h₁⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 := by
      apply Subtype.ext
      show (f : LaurentSeries (AlgebraicClosure ℚ)) = 0
      calc (f : LaurentSeries (AlgebraicClosure ℚ))
          = ((0 : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by rw [hf0]
        _ = 0 := Subfield.coe_zero _
    rw [hz]; exact map_zero _
  have hfW : f ∈ W.toValuationSubring := (hWiff f hfK).mp ⟨p, s, hs𝔭, hfsp⟩
  have hfinvK : (f⁻¹ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K :=
    (fieldOver (1 * q) K).inv_mem hfK
  have hval1 : W.adicValuation f = 1 :=
    withZero_eq_one_of_log_eq_zero _ (W.adicValuation_ne_zero hf0)
      (by have := hord; unfold Place.ord at this; omega)
  have hfinvW : f⁻¹ ∈ W.toValuationSubring :=
    inv_mem_of_isUnit W.toValuationSubring f hfW
      ((W.adicValuation_coe_eq_one_iff _).mp hval1)
  have hWfi := (hWiff f⁻¹ hfinvK).mpr hfinvW
  obtain ⟨r', s', hs'𝔭, hfs'⟩ := hWfi
  have hf0L : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hf0 (by
    apply Subtype.ext; rw [h]; exact (Subfield.coe_zero _).symm)
  have hs'fr : (s' : LaurentSeries (AlgebraicClosure ℚ)) =
      (f : LaurentSeries (AlgebraicClosure ℚ)) * (r' : LaurentSeries (AlgebraicClosure ℚ)) := by
    have hcoe : ((f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := by
      exact_mod_cast rfl
    rw [hcoe, inv_mul_eq_iff_eq_mul₀ hf0L] at hfs'
    exact hfs'
  have key : s' * s = p * r' := by
    apply Subtype.ext
    show (s' : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
      (p : LaurentSeries (AlgebraicClosure ℚ)) * (r' : LaurentSeries (AlgebraicClosure ℚ))
    rw [hs'fr, ← hfsp]; ring
  have hin : p * r' ∈ 𝔭 := 𝔭.mul_mem_right r' hp𝔭
  have hout : s' * s ∉ 𝔭 := fun h => (hpr.mem_or_mem h).elim hs'𝔭 hs𝔭
  exact hout (key ▸ hin)

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring)) :
    ∃ W₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        ((∃ x : A, red x = a ∧
            0 < W₀.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W₀.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) ∧ W₀.ord f ≠ 0 := by
  by_contra hcon
  have hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0 :=
    fun W hW => Classical.byContradiction fun hne => hcon ⟨W, hW, hne⟩

  have hq : 5 ≤ q := by
    by_contra hlt
    rcases eq_two_or_eq_three_of_prime_of_lt_five (Fact.out : q.Prime) (not_le.mp hlt) with rfl | rfl
    · exact h0 (ModularCurve.eq_zero_of_mem_ssJSet_two a ha ha2)
    · exact h0 (ModularCurve.eq_zero_of_mem_ssJSet_three a ha ha2)
  have hred_a : a ∈ Set.range red := mem_range_red_of_pow_q_sq_eq_self red hker a ha2
  have hD :=
    ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq A red a hred_a f
  obtain ⟨K, hKfd, hfK, hx⟩ := hD
  haveI := hKfd
  exact core red hker a ha ha2 h0 h1728 f h₁ h₁F h₁u h₂ h₂F h₂u hmem hnu hford hq K hx hfK

#print axioms solution

end
end S_ModularCurve_NodeLocalized_exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair (solution)
