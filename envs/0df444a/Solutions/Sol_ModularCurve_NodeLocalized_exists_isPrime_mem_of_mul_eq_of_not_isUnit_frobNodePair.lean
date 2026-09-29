-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_isPrime_mem_of_mul_eq_of_not_isUnit_frobNodePair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/62853ada-1224-5406-9b2f-3b6a06349f5b

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
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_isPrime_mem_of_mul_eq_of_not_isUnit_frobNodePair
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.NodeLocalized.coe_modularEvalAt AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false

noncomputable section

private theorem ord_nonneg_of_mem_place {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem ord_pos_of_residue_eq_zero_place {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (h : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0) : 0 < v.ord f := by
  have hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.residue_eq_zero_iff _).mp h
  have hlt' : v.adicValuation f < 1 := (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mp hm
  have hge := ord_nonneg_of_mem_place v hf
  rcases lt_or_eq_of_le hge with h' | h'
  · exact h'
  · exact absurd ((v.ord_eq_zero_iff_adicValuation_eq_one hf0).mp h'.symm) (ne_of_lt hlt')

open AlgebraicCurve IsLocalRing ModularCurve
p2m_open "ModularCurve.NodeLocalized~sub_C_eval_mem_span"

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

private theorem mem_of_isIntegral_of_mul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (c : LaurentSeries (AlgebraicClosure ℚ))
    (hInt : IsIntegral
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) c)
    (hIC : IsIntegrallyClosed
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (y z : LaurentSeries (AlgebraicClosure ℚ))
    (hy : y ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hz : z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hz0 : z ≠ 0) (hfz : c * z = y) :
    c ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  set R₀K := modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
  haveI hRdom : IsDomain ↥R₀K := Subring.instIsDomainSubtypeMem _
  have hginj : Function.Injective R₀K.subtype := Subtype.val_injective
  let ψ : FractionRing ↥R₀K →+* LaurentSeries (AlgebraicClosure ℚ) := IsFractionRing.lift hginj
  have hψinj : Function.Injective ψ := RingHom.injective ψ
  have hψalg : ∀ r : ↥R₀K,
      ψ (algebraMap ↥R₀K (FractionRing ↥R₀K) r) = R₀K.subtype r := fun r => by
    show IsFractionRing.lift hginj (algebraMap ↥R₀K (FractionRing ↥R₀K) r) = R₀K.subtype r
    exact IsFractionRing.lift_algebraMap (K := FractionRing ↥R₀K) hginj r
  have hzR : (⟨z, hz⟩ : ↥R₀K) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  let f₀ : FractionRing ↥R₀K :=
    IsLocalization.mk' _ (⟨y, hy⟩ : ↥R₀K) ⟨⟨z, hz⟩, mem_nonZeroDivisors_of_ne_zero hzR⟩
  have hψf₀ : ψ f₀ = c := by
    have hspec := IsLocalization.mk'_spec (FractionRing ↥R₀K)
      (⟨y, hy⟩ : ↥R₀K) ⟨⟨z, hz⟩, mem_nonZeroDivisors_of_ne_zero hzR⟩
    have hψspec := congrArg ψ hspec
    rw [map_mul, hψalg, hψalg] at hψspec
    have : ψ f₀ * z = y := hψspec
    have hfz' : c * z = y := hfz
    have := this.trans hfz'.symm
    exact mul_right_cancel₀ hz0 this
  have hIntf₀ : IsIntegral ↥R₀K f₀ := by
    obtain ⟨P, hPm, hPf⟩ := hInt
    refine ⟨P, hPm, ?_⟩
    apply hψinj
    rw [map_zero, Polynomial.hom_eval₂, hψf₀]
    have hcomp : ψ.comp (algebraMap ↥R₀K (FractionRing ↥R₀K)) = R₀K.subtype :=
      RingHom.ext fun r => (RingHom.comp_apply _ _ _).trans (hψalg r)
    rw [hcomp]
    exact hPf
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥R₀K)).mp hIntf₀
  have heq : c =
      R₀K.subtype r := by
    rw [← hψf₀, ← hr]; exact hψalg r
  rw [heq]; exact r.2

private theorem jRing_le_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jRing A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  refine Subring.closure_le.mpr ?_
  rintro y (⟨c, rfl⟩ | rfl)
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) = CharPReduction.constSeries (coeffSubring A K) c :=
      MvPolynomial.eval₂Hom_C _ _ c
    rw [← h]
    exact modularEval_mem_modularLocalizedAtPoint _ _ _ _ _ _
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = jqModC (AlgebraicClosure ℚ) :=
      MvPolynomial.eval₂Hom_X' _ _ 0
    rw [← h]
    exact modularEval_mem_modularLocalizedAtPoint _ _ _ _ _ _

private theorem jIntegralClosure_le_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    jIntegralClosure (1 * q) A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  intro c hc
  obtain ⟨hcF, hcInt⟩ := hc
  have hIC : IsIntegrallyClosed
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728 red a ha ha2 hq h0 h1728 K
      ⟨x, hx⟩
  have hle := jRing_le_modularLocalizedAtPoint (q := q) red a K
  have hInt : IsIntegral
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) c := by
    obtain ⟨P, hPm, hPe⟩ := hcInt
    refine ⟨P.map (Subring.inclusion hle), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
        (LaurentSeries (AlgebraicClosure ℚ))).comp (Subring.inclusion hle) =
        algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) := RingHom.ext fun _ => rfl
    rw [hcomp]
    exact hPe
  obtain ⟨y, z, hy, hz, hz0, hcz⟩ := ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver red a K hcF
  exact mem_of_isIntegral_of_mul_eq red a K c hInt hIC y z hy hz hz0 hcz

private theorem sub_C_eval_mem_span {R S : Type*} [CommRing R] [CommRing S]
    (φ : MvPolynomial (Fin 2) R →+* S) (x₀ x₁ : R) (t : MvPolynomial (Fin 2) R) :
    φ t - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] t)) ∈
      Ideal.span {φ (MvPolynomial.X 0 - MvPolynomial.C x₀), φ (MvPolynomial.X 1 - MvPolynomial.C x₁)} := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.eval_C, sub_self]
    exact Ideal.zero_mem _
  | add p r hp hr =>
    rw [MvPolynomial.eval_add, MvPolynomial.C_add, map_add, map_add]
    have h : φ p + φ r - (φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p)) +
        φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] r))) =
        (φ p - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p))) +
        (φ r - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] r))) := by ring
    rw [h]
    exact Ideal.add_mem _ hp hr
  | mul_X p n hp =>
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.C_mul, map_mul, map_mul]
    have h : φ p * φ (MvPolynomial.X n) -
        φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p)) * φ (MvPolynomial.C (![x₀, x₁] n)) =
        φ p * (φ (MvPolynomial.X n) - φ (MvPolynomial.C (![x₀, x₁] n))) +
        (φ p - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p))) * φ (MvPolynomial.C (![x₀, x₁] n)) := by ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ hp)
    rw [← map_sub]
    fin_cases n
    · exact Ideal.subset_span (Or.inl rfl)
    · exact Ideal.subset_span (Or.inr rfl)

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

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (hq : 5 ≤ q)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (p s : ↥(jIntegralClosure (1 * q) A K))
    (hfsp : (f : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
      (p : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ 𝔫 : Ideal ↥(jIntegralClosure (1 * q) A K), 𝔫.IsPrime ∧ p ∈ 𝔫 ∧
      (∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0 →
          ∀ ht : modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K,
            (⟨_, ht⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔫) := by
  classical
  obtain ⟨-, hloc, -, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hloc
  have hmax' := hmax
  have hCle := jIntegralClosure_le_modularLocalizedAtPoint red a ha ha2 h0 h1728 hq K x hx
  let ι := Subring.inclusion hCle
  refine ⟨(IsLocalRing.maximalIdeal _).comap ι, inferInstance, ?_, ?_⟩
  ·
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨w, hw⟩ := hunit.exists_right_inv
    have hpw : (p : LaurentSeries (AlgebraicClosure ℚ)) * (w : LaurentSeries (AlgebraicClosure ℚ)) = 1 :=
      congrArg Subtype.val hw
    have hf0 : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => h₁u (by
      rw [show (⟨_, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = 0 from Subtype.ext h, map_zero])
    have hfsw : (f : LaurentSeries (AlgebraicClosure ℚ)) *
        ((s : LaurentSeries (AlgebraicClosure ℚ)) * (w : LaurentSeries (AlgebraicClosure ℚ))) = 1 := by
      rw [← mul_assoc, hfsp, hpw]
    have hfinv : (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ =
        (s : LaurentSeries (AlgebraicClosure ℚ)) * (w : LaurentSeries (AlgebraicClosure ℚ)) :=
      inv_eq_of_mul_eq_one_right hfsw
    have hgR : (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈
        modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
      rw [hfinv]; exact mul_mem (hCle s.2) w.2
    have hg₁ : (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
      inv_mem_modularLocalized_of_ne_zero _ _ red h₁ h₁u
    have hmul : (⟨_, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) * ⟨_, hg₁⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hf0)
    have hred_inv : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁⟩ =
        (CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩)⁻¹ := by
      have h := congrArg (CharPReduction.modularRedLocHom (1 * q) A.toSubring red) hmul
      rw [map_mul, map_one] at h
      exact eq_inv_of_mul_eq_one_right h
    have hg₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁⟩ ∈ modularFunctionFieldC k 1 := by
      rw [hred_inv]; exact inv_mem h₁F
    have hg0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁⟩ ≠ 0 := by
      rw [hred_inv]; exact inv_ne_zero h₁u
    have h33 := (ModularCurve.NodeLocalized.natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow red a ha2 K ϖ hϖ
      ⟨_, hgR⟩ hg₁ hg₁F hg0 0).mpr (by rw [pow_zero, Ideal.span_singleton_one, sup_top_eq]; exact Submodule.mem_top)
    have h33' : ((0 : ℕ) : ℤ) ≤ (frobNodePair q a).1.ord (⟨_, hg₁F⟩ : ↥(modularFunctionFieldC k 1)) := h33
    have hel : (⟨_, hg₁F⟩ : ↥(modularFunctionFieldC k 1)) = (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1))⁻¹ :=
      Subtype.ext (by rw [IntermediateField.coe_inv]; exact hred_inv)
    have hfbar0 : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := fun h => h₁u (congrArg Subtype.val h)
    have hres : IsLocalRing.residue (frobNodePair q a).1.toValuationSubring ⟨_, hmem⟩ = 0 := by
      by_contra hne
      exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne)
    have hpos := ord_pos_of_residue_eq_zero_place (frobNodePair q a).1 hmem hfbar0 hres
    rw [hel, Place.ord_inv, Nat.cast_zero] at h33'
    omega
  ·
    intro t ht htC hmemb
    rw [Ideal.mem_comap] at hmemb
    let φ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+*
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
      (modularEval (1 * q) (coeffSubring A K)).codRestrict _
        (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    have hιφ : ι ⟨_, htC⟩ = φ t := Subtype.ext rfl
    rw [hιφ] at hmemb
    have hgen0 : φ (MvPolynomial.X 0 - MvPolynomial.C x) ∈ IsLocalRing.maximalIdeal _ := by
      rw [hmax']
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hgen1 : φ (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)) ∈ IsLocalRing.maximalIdeal _ := by
      rw [hmax']
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hle : Ideal.span {φ (MvPolynomial.X 0 - MvPolynomial.C x), φ (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} ≤
        IsLocalRing.maximalIdeal _ := by
      rw [Ideal.span_le]
      rintro g (rfl | rfl)
      · exact hgen0
      · exact hgen1
    have htay := sub_C_eval_mem_span φ x (x ^ q) t
    have hCmem : φ (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] t)) ∈ IsLocalRing.maximalIdeal _ := by
      have h := Ideal.sub_mem _ hmemb (hle htay)
      rwa [sub_sub_cancel] at h
    have hc : redRestrict red K (MvPolynomial.eval ![x, x ^ q] t) =
        pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t := by
      show redRestrict red K (MvPolynomial.eval₂ (RingHom.id _) ![x, x ^ q] t) =
        MvPolynomial.eval₂ (redRestrict red K) ![a, a ^ q] t
      rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
      congr 1
      funext i
      fin_cases i
      · exact hx
      · show redRestrict red K (x ^ q) = a ^ q
        rw [map_pow, hx]
    obtain ⟨d, hd⟩ := exists_mul_eq_one_of_redRestrict_ne_zero red hker K (MvPolynomial.eval ![x, x ^ q] t)
      (by rw [hc]; exact ht)
    have hu : IsUnit (φ (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] t))) :=
      IsUnit.of_mul_eq_one (φ (MvPolynomial.C d)) (by rw [← map_mul, ← MvPolynomial.C_mul, hd, MvPolynomial.C_1, map_one])
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hCmem hu)

end

#print axioms solution

end S_ModularCurve_NodeLocalized_exists_isPrime_mem_of_mul_eq_of_not_isUnit_frobNodePair
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_isPrime_mem_of_mul_eq_of_not_isUnit_frobNodePair (solution)
