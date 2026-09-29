-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_heightOne_mem_of_mul_eq_of_not_isUnit_frobNodePair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e2b21557-b03c-567c-b8a7-51bd74c46797

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ModularCurve_NodeLocalized_exists_isPrime_mem_of_mul_eq_of_not_isUnit_frobNodePair
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherian_and_isLocalization
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_heightOne_mem_of_mul_eq_of_not_isUnit_frobNodePair
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.NodeLocalized.coe_modularEvalAt AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

private theorem inv_mem_modularLocalized_of_ne_zero (N : ℕ) [NeZero N] (A : Subring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] (red : A →+* k) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularLocalized N A red)
    (hu : CharPReduction.modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) :
    x⁻¹ ∈ CharPReduction.modularLocalized N A red := by
  obtain ⟨r, s, hs, hxs⟩ := id hx
  have hx0 : x ≠ 0 := fun h => hu (by
    rw [show (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) = 0 from Subtype.ext h, map_zero])
  have hloc : CharPReduction.redLoc (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) ≠ 0 := fun h0 =>
    hu (by rw [show CharPReduction.modularRedLocHom N A red ⟨x, hx⟩ = CharPReduction.redLoc ⟨x, hx⟩ from
      CharPReduction.redLocHom_apply _]; exact h0)
  have hspec := CharPReduction.redLoc_spec (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) hxs
  have hr : r ∉ CharPReduction.redKer A red (CharPReduction.modularRing N A)
      (CharPReduction.modularRing_le_integralCoeffs N A) := by
    rw [CharPReduction.notMem_redKer_iff] at hs ⊢
    rw [← hspec]
    exact mul_ne_zero hloc hs
  refine (CharPReduction.mem_localizedAtKer _ _ _ _).mpr ⟨s, r, hr, ?_⟩
  rw [← hxs, inv_mul_cancel_left₀ hx0]

private theorem eq_two_or_eq_three_of_prime_of_lt_five {q : ℕ} (hp : q.Prime) (hq : q < 5) :
    q = 2 ∨ q = 3 := by
  have h2 := hp.two_le
  interval_cases q
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hp (by norm_num)

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (p s : ↥(jIntegralClosure (1 * q) A K)) (s₀ : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs_eq : (s : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) s₀)
    (hps0 : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s₀ ≠ 0)
    (hfsp : (f : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
      (p : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) (_ : 𝔭.IsPrime), 𝔭.height = 1 ∧
      ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 ∧ p ∈ 𝔭 ∧
      (∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0 →
          ∀ ht : modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K,
            (⟨_, ht⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) := by
  classical
  have hq : 5 ≤ q := by
    by_contra hlt
    rcases eq_two_or_eq_three_of_prime_of_lt_five (Fact.out : q.Prime) (not_le.mp hlt) with rfl | rfl
    · exact h0 (ModularCurve.eq_zero_of_mem_ssJSet_two a ha ha2)
    · exact h0 (ModularCurve.eq_zero_of_mem_ssJSet_three a ha ha2)
  obtain ⟨𝔫, h𝔫, hp𝔫, hS𝔫⟩ :=
    exists_isPrime_mem_of_mul_eq_of_not_isUnit_frobNodePair red hker a ha ha2 h0 h1728 hq f h₁ h₁F h₁u hmem hnu K
      x hx ϖ hϖ p s hfsp

  have ht : modularEval (1 * q) (coeffSubring A K) s₀ ∈ jIntegralClosure (1 * q) A K := hs_eq ▸ s.2
  have hs𝔫 : s ∉ 𝔫 := by
    rw [show s = ⟨modularEval (1 * q) (coeffSubring A K) s₀, ht⟩ from Subtype.ext hs_eq]
    exact hS𝔫 s₀ hps0 ht

  have hf0 : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => h₁u (by
    rw [show (⟨_, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = 0 from Subtype.ext h, map_zero])
  have hs0 : (s : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h =>
    hs𝔫 (by rw [show s = 0 from Subtype.ext h]; exact 𝔫.zero_mem)
  have hp0 : p ≠ 0 := fun h => by
    have h' := hfsp
    rw [h, ZeroMemClass.coe_zero] at h'
    exact mul_ne_zero hf0 hs0 h'

  haveI := h𝔫
  obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr hp𝔫)
  have h𝔭pr : 𝔭.IsPrime := h𝔭min.1.1
  have hp𝔭 : p ∈ 𝔭 := h𝔭min.1.2 (Ideal.mem_span_singleton_self p)

  haveI hN : IsNoetherianRing ↥(jIntegralClosure (1 * q) A K) := by
    obtain ⟨data, -⟩ := ModularCurve.exists_modularPolynomialData_evalSymm q
    exact (ModularCurve.jIntegralClosure_isNoetherian_and_isLocalization red a data K).1
  haveI : (Ideal.span {p}).IsPrincipal := ⟨⟨p, rfl⟩⟩
  have hle1 : 𝔭.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) 𝔭 h𝔭min
  have hge1 : 1 ≤ 𝔭.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hp0)).trans
      (Ideal.height_mono h𝔭min.1.2)
  have hht : 𝔭.height = 1 := le_antisymm hle1 hge1

  have hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 := by
    intro hq𝔭
    haveI := h𝔭pr
    have hg : ((f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        fieldOver (1 * q) K := by
      rw [IntermediateField.coe_inv]; exact inv_mem hfK
    have hg₁ : ((f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [IntermediateField.coe_inv]; exact inv_mem_modularLocalized_of_ne_zero _ _ _ h₁ h₁u
    have hg₂ : ((frickeInvolutionBar (1 * q) f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [map_inv₀, IntermediateField.coe_inv]; exact inv_mem_modularLocalized_of_ne_zero _ _ _ h₂ h₂u
    obtain ⟨r₁, s₁, hs₁, hr₁⟩ :=
      ModularCurve.exists_mul_eq_of_height_one_of_natCast_mem red K 𝔭 hht hq𝔭 f⁻¹ hg hg₁ hg₂
    rw [IntermediateField.coe_inv] at hr₁
    have hs₁f : (s₁ : LaurentSeries (AlgebraicClosure ℚ)) =
        (f : LaurentSeries (AlgebraicClosure ℚ)) * (r₁ : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [← hr₁, mul_inv_cancel_left₀ hf0]
    have hC : s₁ * s = p * r₁ := Subtype.ext (by
      show (s₁ : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
        (p : LaurentSeries (AlgebraicClosure ℚ)) * (r₁ : LaurentSeries (AlgebraicClosure ℚ))
      rw [hs₁f, ← hfsp]; ring)
    have hmul : s₁ * s ∈ 𝔭 := hC ▸ Ideal.mul_mem_right _ _ hp𝔭
    rcases h𝔭pr.mem_or_mem hmul with h | h
    · exact hs₁ h
    · exact hs𝔫 (h𝔭le h)
  exact ⟨𝔭, h𝔭pr, hht, hq𝔭, hp𝔭, fun t ht0 ht' hmem => hS𝔫 t ht0 ht' (h𝔭le hmem)⟩

#print axioms solution

end S_ModularCurve_NodeLocalized_exists_heightOne_mem_of_mul_eq_of_not_isUnit_frobNodePair
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_heightOne_mem_of_mul_eq_of_not_isUnit_frobNodePair (solution)
