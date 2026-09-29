-- Prove2me | solution 1 for ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/32bf5985-5742-5aff-b039-aaa18c9e51e7

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_modularEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_pointEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728.ModularCurve"
open ModularCurve.NodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full ssJSet jWidth modularFunctionFieldBar reduceModBivar modularEval_kroneckerRemainder pointEval_kroneckerRemainder eval_kroneckerRemainder_ne_zero_of_mem_ssJSet NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero exists_kroneckerCongruence_of_prime NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728 NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint"
p2m_open "ModularCurve"
namespace ChartKAssembly

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Defs
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

abbrev R₀ : Subring LQ :=
  modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)

abbrev ev (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : ↥(R₀ q A red a K) :=
  ⟨modularEval (1 * q) (coeffSubring A K) p,
    modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p⟩

def evHom : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(R₀ q A red a K) :=
  (modularEval (1 * q) (coeffSubring A K)).codRestrict (R₀ q A red a K)
    (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))

theorem evHom_apply (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : evHom q A red a K p = ev q A red a K p := rfl

def constHom : ↥(coeffSubring A K) →+* ↥(R₀ q A red a K) :=
  (evHom q A red a K).comp MvPolynomial.C

theorem constHom_apply (c : ↥(coeffSubring A K)) :
    constHom q A red a K c = ev q A red a K (MvPolynomial.C c) := rfl

end Defs

section RedLemmas
variable {A : ValuationSubring Qb} {k : Type*} [Field k]

theorem mem_coeffSubring_iff' (K : IntermediateField ℚ Qb) {x : Qb} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

theorem red_eq_zero_of_mem_maximalIdeal (red : A →+* k) (q : ℕ) [Fact q.Prime] [CharP k q] (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
  have hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hA : A.LiesOverPrime q := by
    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff]
    have hnu : ¬ IsUnit (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) := by
      intro hu
      have h1 := hu.map red
      have h0 : red ⟨(q : AlgebraicClosure ℚ), hq⟩ = 0 := by
        have : (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
        rw [this, map_natCast, CharP.cast_eq_zero]
      rw [h0] at h1
      exact not_isUnit_zero h1
    exact (ValuationSubring.valuation_lt_one_iff A ⟨(q : AlgebraicClosure ℚ), hq⟩).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  exact ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red τ
    ((ValuationSubring.valuation_lt_one_iff A τ).mp hτ)

theorem isUnit_coeffSubring_iff (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    (c : ↥(coeffSubring A K)) : IsUnit c ↔ redRestrict red K c ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ hc
    have h1 : redRestrict red K ((u * u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) = 1 := by
      rw [mul_inv_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, hc, zero_mul] at h1
    exact zero_ne_one h1
  · intro hc
    have hcA : (c : Qb) ∈ A := ((mem_coeffSubring_iff' (A := A) K).mp c.2).1
    have hcK : (c : Qb) ∈ K := ((mem_coeffSubring_iff' (A := A) K).mp c.2).2
    have hcm : (⟨(c : Qb), hcA⟩ : A) ∉ IsLocalRing.maximalIdeal A := fun hm =>
      hc (red_eq_zero_of_mem_maximalIdeal red q _ hm)
    have hu : IsUnit (⟨(c : Qb), hcA⟩ : A) := by
      by_contra h; exact hcm ((IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨u, hu⟩ := hu
    have hmul : (((u⁻¹ : Aˣ) : A) : Qb) * (c : Qb) = 1 := by
      have h := congrArg (fun z : A => (z : Qb)) u.inv_mul
      rw [hu] at h
      simpa using h
    have hinv : (c : Qb)⁻¹ = (((u⁻¹ : Aˣ) : A) : Qb) := inv_eq_of_mul_eq_one_left hmul
    have hinvmem : (c : Qb)⁻¹ ∈ coeffSubring A K :=
      (mem_coeffSubring_iff' (A := A) K).mpr ⟨hinv ▸ ((u⁻¹ : Aˣ) : A).2, K.inv_mem hcK⟩
    have hc0 : (c : Qb) ≠ 0 := by
      rintro h0
      apply hc
      have : c = 0 := Subtype.ext h0
      rw [this, map_zero]
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩

theorem stepA_dvr (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] : IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : Qb)⁻¹ ∈ coeffSubring A K := by
      rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : Qb)⁻¹ ∈ K)
    have hu : IsUnit (((q : ℕ) : ↥(coeffSubring A K))) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hqK⟩, Subtype.ext (by
        push_cast
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))⟩
    have := (isUnit_coeffSubring_iff red K q _).mp hu
    apply this
    rw [map_natCast, CharP.cast_eq_zero]
  · exact h

theorem stepA_uniformizer (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), Irreducible ϖ ∧ (∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) ∧
      ∃ (e : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ e ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ e * ε := by
  classical
  haveI := stepA_dvr red K q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
  have hker : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
    intro c
    have h1 : redRestrict red K c = 0 ↔ ¬ IsUnit c := by
      rw [isUnit_coeffSubring_iff red K q c, not_not]
    rw [h1, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact Iff.rfl
  refine ⟨ϖ, hϖ, hker, ?_⟩
  have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h
    push_cast at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine ⟨n, u, ?_, u.isUnit, by rw [hn, mul_comm]⟩
  by_contra hlt
  have hn0 : n = 0 := by omega
  rw [hn0, pow_zero, mul_one] at hn
  have hu : IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := hn ▸ u.isUnit
  exact ((isUnit_coeffSubring_iff red K q _).mp hu) (by rw [map_natCast, CharP.cast_eq_zero])

end RedLemmas

section Frac
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

def fracField (S : Subring LQ) : Subfield LQ where
  carrier := {x | ∃ y z : LQ, y ∈ S ∧ z ∈ S ∧ z ≠ 0 ∧ x * z = y}
  zero_mem' := ⟨0, 1, zero_mem S, one_mem S, one_ne_zero, by ring⟩
  one_mem' := ⟨1, 1, one_mem S, one_mem S, one_ne_zero, by ring⟩
  add_mem' := by
    rintro x x' ⟨y, z, hy, hz, hz0, hxz⟩ ⟨y', z', hy', hz', hz0', hxz'⟩
    refine ⟨y * z' + y' * z, z * z', add_mem (mul_mem hy hz') (mul_mem hy' hz), mul_mem hz hz',
      mul_ne_zero hz0 hz0', ?_⟩
    calc (x + x') * (z * z') = x * z * z' + x' * z' * z := by ring
      _ = y * z' + y' * z := by rw [hxz, hxz']
  neg_mem' := by
    rintro x ⟨y, z, hy, hz, hz0, hxz⟩
    exact ⟨-y, z, neg_mem hy, hz, hz0, by rw [neg_mul, hxz]⟩
  mul_mem' := by
    rintro x x' ⟨y, z, hy, hz, hz0, hxz⟩ ⟨y', z', hy', hz', hz0', hxz'⟩
    refine ⟨y * y', z * z', mul_mem hy hy', mul_mem hz hz', mul_ne_zero hz0 hz0', ?_⟩
    calc x * x' * (z * z') = (x * z) * (x' * z') := by ring
      _ = y * y' := by rw [hxz, hxz']
  inv_mem' := by
    rintro x ⟨y, z, hy, hz, hz0, hxz⟩
    by_cases hx : x = 0
    · exact ⟨0, 1, zero_mem S, one_mem S, one_ne_zero, by rw [hx, inv_zero, zero_mul]⟩
    · refine ⟨z, y, hz, hy, ?_, ?_⟩
      · rw [← hxz]; exact mul_ne_zero hx hz0
      · rw [← hxz, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

omit [Fact q.Prime] in
theorem mem_fracField_iff (S : Subring LQ) (x : LQ) :
    x ∈ fracField S ↔ ∃ y z : LQ, y ∈ S ∧ z ∈ S ∧ z ≠ 0 ∧ x * z = y := Iff.rfl

theorem stepH_fieldOver_le : fieldOver (1 * q) K ≤ fracField (R₀ q A red a K) := by
  unfold fieldOver
  rw [Subfield.closure_le]
  rintro x (⟨c, rfl⟩ | rfl | rfl)
  ·
    rcases A.mem_or_inv_mem (c : Qb) with hc | hc
    · refine ⟨_, 1, (ev q A red a K (MvPolynomial.C ⟨(c : Qb), hc, c.2⟩)).2, one_mem _, one_ne_zero, ?_⟩
      rw [mul_one]; simp [modularEval]; rfl
    · by_cases hc0 : (c : Qb) = 0
      · refine ⟨0, 1, zero_mem _, one_mem _, one_ne_zero, ?_⟩
        show algebraMap Qb LQ (c : Qb) * 1 = 0
        rw [mul_one, hc0, map_zero]
      · refine ⟨1, _, one_mem _, (ev q A red a K (MvPolynomial.C ⟨(c : Qb)⁻¹, hc, K.inv_mem c.2⟩)).2, ?_, ?_⟩
        · simp [modularEval, CharPReduction.constSeries, hc0]
        · show algebraMap Qb LQ (c : Qb) * modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C _) = 1
          rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
          show algebraMap Qb LQ (c : Qb) * algebraMap Qb LQ (c : Qb)⁻¹ = 1
          rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  · exact ⟨_, 1, (ev q A red a K (MvPolynomial.X 0)).2, one_mem _, one_ne_zero, by rw [mul_one]; simp [modularEval]⟩
  · exact ⟨_, 1, (ev q A red a K (MvPolynomial.X 1)).2, one_mem _, one_ne_zero, by rw [mul_one]; simp [modularEval]⟩

theorem stepI_mem_of_isIntegral (hic : IsIntegrallyClosed ↥(R₀ q A red a K)) {x : LQ} (hxF : x ∈ fieldOver (1 * q) K)
    (hint : IsIntegral ↥(R₀ q A red a K) x) : x ∈ R₀ q A red a K := by
  classical
  obtain ⟨y, z, hy, hz, hz0, hxz⟩ := stepH_fieldOver_le q A red a K hxF
  set R := R₀ q A red a K with hR
  have hinj : Function.Injective (algebraMap ↥R LQ) := Subtype.val_injective
  let φ : FractionRing ↥R →ₐ[↥R] LQ :=
    { IsFractionRing.lift hinj with commutes' := fun r => IsFractionRing.lift_algebraMap hinj r }
  have hφ : Function.Injective φ := φ.toRingHom.injective
  let w : FractionRing ↥R := algebraMap ↥R _ ⟨y, hy⟩ / algebraMap ↥R _ ⟨z, hz⟩
  have hw : φ w = x := by
    have h1 : φ (algebraMap ↥R _ ⟨y, hy⟩) = y := IsFractionRing.lift_algebraMap hinj _
    have h2 : φ (algebraMap ↥R _ ⟨z, hz⟩) = z := IsFractionRing.lift_algebraMap hinj _
    rw [map_div₀, h1, h2, div_eq_iff hz0, hxz]
  have hwint : IsIntegral ↥R w := by
    rw [← isIntegral_algHom_iff φ hφ, hw]; exact hint
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥R) (K := FractionRing ↥R)).mp hwint
  have : (r : LQ) = x := by
    rw [← hw, ← hr]; exact (IsFractionRing.lift_algebraMap hinj r).symm
  rw [← this]; exact r.2

end Frac

section KronValue

theorem mem_range_of_pow_eq {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) {k' : Type*} [Field k'] (ι : k →+* k') (y : k') (hy : ∃ n : ℕ, 0 < n ∧ y ^ (q ^ n) = y) :
    y ∈ ι.range := by
  classical
  obtain ⟨n, hn, hy⟩ := hy
  haveI : IsLocalHom red := ⟨fun τ hτ => by
    by_contra hτu
    have h0 := red_eq_zero_of_mem_maximalIdeal red q τ ((IsLocalRing.mem_maximalIdeal _).mpr hτu)
    rw [h0] at hτ
    exact not_isUnit_zero hτ⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  let θ : IsLocalRing.ResidueField A →+* k := IsLocalRing.ResidueField.lift red
  let p : Polynomial (IsLocalRing.ResidueField A) := Polynomial.X ^ (q ^ n) - Polynomial.X
  have hdeg : (Polynomial.X : Polynomial (IsLocalRing.ResidueField A)).degree < ((q ^ n : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_X]
    have : 1 < q ^ n := Nat.one_lt_pow hn.ne' (Fact.out : q.Prime).one_lt
    exact_mod_cast this
  have hmonic : p.Monic := Polynomial.monic_X_pow_sub hdeg
  have hp0 : p ≠ 0 := hmonic.ne_zero
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hroots : (p.map (ι.comp θ)).roots = p.roots.map (ι.comp θ) := hsplit.roots_map (ι.comp θ)
  have hy' : y ∈ (p.map (ι.comp θ)).roots := by
    rw [Polynomial.mem_roots (Polynomial.map_monic_ne_zero hmonic)]
    simp [p, hy]
  rw [hroots, Multiset.mem_map] at hy'
  obtain ⟨r, -, rfl⟩ := hy'
  exact ⟨θ r, rfl⟩

theorem kron_value_ne_zero {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]
    [DecidableEq k] (red : A →+* k) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q) (h0 : a ≠ 0)
    (h1728 : a ≠ 1728) (data : ModularPolynomialData q) (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) +
      Polynomial.C (Polynomial.C (q : ℤ)) * R) :
    ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a ≠ 0 := by
  classical
  let k' := AlgebraicClosure k
  let ι : k →+* k' := algebraMap k k'
  haveI : CharP k' q := charP_of_injective_algebraMap ι.injective q
  have hk : ∀ y : k', (∃ n : ℕ, 0 < n ∧ y ^ (q ^ n) = y) → y ∈ (algebraMap k k').range :=
    fun y hy => mem_range_of_pow_eq red ι y hy
  have ha' : algebraMap k k' a ∈ ssJSet q k' :=
    ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728 hk a ha ha2 hq h0 h1728
  have h0' : ι a ≠ 0 := (map_ne_zero ι).mpr h0
  have h1728' : ι a ≠ 1728 := by
    intro h
    apply h1728
    apply ι.injective
    rw [h, map_ofNat]
  have hK2 := ModularCurve.eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hq data R hR (ι a) ha' h0' h1728'
  intro hval
  apply hK2

  set P := R.map (Polynomial.mapRingHom (Int.castRingHom k)) with hP
  have hcast : Int.castRingHom k' = ι.comp (Int.castRingHom k) := RingHom.ext_int _ _
  have hmap : R.map (Polynomial.mapRingHom (Int.castRingHom k')) = P.map (Polynomial.mapRingHom ι) := by
    rw [hcast, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map]
  rw [hmap, ← map_pow, show Polynomial.C (ι (a ^ q)) = Polynomial.mapRingHom ι (Polynomial.C (a ^ q)) by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C], Polynomial.eval_map, Polynomial.eval₂_hom,
    Polynomial.coe_mapRingHom, Polynomial.eval_map, Polynomial.eval₂_hom, hval, map_zero]

end KronValue

section Steps
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]
variable (red : A →+* k) (a : k) (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem geom_congr {R : Type*} [CommRing R] (u v : R) (n : ℕ) :
    (u - v) ∣ (∑ i ∈ Finset.range n, u ^ i * v ^ (n - 1 - i)) - n * v ^ (n - 1) := by
  have : (n : R) * v ^ (n - 1) = ∑ i ∈ Finset.range n, v ^ i * v ^ (n - 1 - i) := by
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))])]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [this, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  rw [← sub_mul]
  exact Dvd.dvd.mul_right (sub_dvd_pow_sub_pow u v i) _

theorem stepC_maximalIdeal_eq (ha2 : a ^ (q ^ 2) = a) (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    [IsLocalRing ↥(R₀ q A red a K)] [IsNoetherianRing ↥(R₀ q A red a K)]
    (hmax : maximalIdeal ↥(R₀ q A red a K) =
      Ideal.span {ev q A red a K (MvPolynomial.C ϖ), ev q A red a K (MvPolynomial.X 0 - MvPolynomial.C x),
        ev q A red a K (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))}) :
    maximalIdeal ↥(R₀ q A red a K) =
      Ideal.span {ev q A red a K (MvPolynomial.C ϖ), ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)} := by
  classical
  set E := evHom q A red a K with hE
  set cϖ := E (MvPolynomial.C ϖ) with hcϖ
  set J := E (MvPolynomial.X 0) with hJ
  set Jq := E (MvPolynomial.X 1) with hJq
  set cx := E (MvPolynomial.C x) with hcx
  have hX : E (MvPolynomial.X 0 - MvPolynomial.C x) = J - cx := by simp only [map_sub, J, cx]
  have hY : E (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)) = Jq - cx ^ q := by simp only [map_sub, map_pow, Jq, cx]
  have hG : E (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) = Jq - J ^ q := by simp only [map_sub, map_pow, J, Jq]
  have hH : E (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) = J - Jq ^ q := by simp only [map_sub, map_pow, J, Jq]
  set 𝔪 := maximalIdeal ↥(R₀ q A red a K) with h𝔪
  have hmax' : 𝔪 = Ideal.span {cϖ, J - cx, Jq - cx ^ q} := by rw [hmax, ← hX, ← hY]; rfl
  change 𝔪 = Ideal.span {E (MvPolynomial.C ϖ), E (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
    E (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)}
  rw [hG, hH]
  set N : Ideal ↥(R₀ q A red a K) := Ideal.span {cϖ, Jq - J ^ q, J - Jq ^ q} with hN

  have m1 : cϖ ∈ 𝔪 := by rw [hmax']; exact Ideal.subset_span (Set.mem_insert _ _)
  have m2 : J - cx ∈ 𝔪 := by rw [hmax']; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have m3 : Jq - cx ^ q ∈ 𝔪 := by
    rw [hmax']; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have n1 : cϖ ∈ N := Ideal.subset_span (Set.mem_insert _ _)
  have n2 : Jq - J ^ q ∈ N := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have n3 : J - Jq ^ q ∈ N := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

  have hred0 : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 → ∀ I : Ideal ↥(R₀ q A red a K), cϖ ∈ I →
      E (MvPolynomial.C c) ∈ I := by
    intro c hc I hI
    obtain ⟨d, rfl⟩ := (hϖ c).mp hc
    rw [map_mul, map_mul]
    exact I.mul_mem_right _ hI
  have hqI : ∀ I : Ideal ↥(R₀ q A red a K), cϖ ∈ I → (q : ↥(R₀ q A red a K)) ∈ I := by
    intro I hI
    have : (q : ↥(R₀ q A red a K)) = E (MvPolynomial.C (q : ↥(coeffSubring A K))) := by
      rw [map_natCast, map_natCast]
    rw [this]
    exact hred0 _ (by rw [map_natCast, CharP.cast_eq_zero]) I hI
  have hxxI : ∀ I : Ideal ↥(R₀ q A red a K), cϖ ∈ I → (cx ^ q) ^ q - cx ∈ I := by
    intro I hI
    have : (cx ^ q) ^ q - cx = E (MvPolynomial.C (x ^ (q * q) - x)) := by
      simp only [map_sub, map_pow, cx, pow_mul]
    rw [this]
    refine hred0 _ ?_ I hI
    rw [map_sub, map_pow, hx, show q * q = q ^ 2 from (sq q).symm, ha2, sub_self]

  have hNle : N ≤ 𝔪 := by
    rw [hN, Ideal.span_le]
    rintro _ (rfl | rfl | rfl)
    · exact m1
    ·
      obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow J cx q
      have : Jq - J ^ q = (Jq - cx ^ q) - (J - cx) * t := by rw [← ht]; ring
      rw [SetLike.mem_coe, this]
      exact Submodule.sub_mem _ m3 (𝔪.mul_mem_right _ m2)
    · obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow Jq (cx ^ q) q
      have : J - Jq ^ q = (J - cx) - (Jq - cx ^ q) * t - ((cx ^ q) ^ q - cx) := by rw [← ht]; ring
      rw [SetLike.mem_coe, this]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ m2 (𝔪.mul_mem_right _ m3)) (hxxI 𝔪 m1)

  have hle : 𝔪 ≤ N ⊔ 𝔪 • 𝔪 := by
    have hL : ∀ u, u ∈ N → u ∈ N ⊔ 𝔪 • 𝔪 := fun u hu => Submodule.mem_sup_left hu
    have hR : ∀ u v, u ∈ 𝔪 → v ∈ 𝔪 → u * v ∈ N ⊔ 𝔪 • 𝔪 := fun u v hu hv =>
      Submodule.mem_sup_right (Submodule.smul_mem_smul hu hv)

    obtain ⟨t, ht⟩ := geom_congr Jq (cx ^ q) q
    obtain ⟨t', ht'⟩ := geom_congr J cx q
    have hS := geom_sum₂_mul Jq (cx ^ q) q
    have hS' := geom_sum₂_mul J cx q
    have e1 : Jq ^ q - (cx ^ q) ^ q = (Jq - cx ^ q) * ((q : ↥(R₀ q A red a K)) * (cx ^ q) ^ (q - 1)) +
        (Jq - cx ^ q) * ((Jq - cx ^ q) * t) := by
      rw [← hS, sub_eq_iff_eq_add.mp ht]; ring
    have e2 : J ^ q - cx ^ q = (J - cx) * ((q : ↥(R₀ q A red a K)) * cx ^ (q - 1)) + (J - cx) * ((J - cx) * t') := by
      rw [← hS', sub_eq_iff_eq_add.mp ht']; ring
    have k2 : J - cx ∈ N ⊔ 𝔪 • 𝔪 := by
      have : J - cx = (J - Jq ^ q) + (Jq ^ q - (cx ^ q) ^ q) + ((cx ^ q) ^ q - cx) := by ring
      rw [this, e1]
      refine Submodule.add_mem _ (Submodule.add_mem _ (hL _ n3) (Submodule.add_mem _ (hL _ ?_) (hR _ _ m3 ?_)))
        (hL _ (hxxI N n1))
      · exact N.mul_mem_left _ (N.mul_mem_right _ (hqI N n1))
      · exact 𝔪.mul_mem_right _ m3
    have k3 : Jq - cx ^ q ∈ N ⊔ 𝔪 • 𝔪 := by
      have : Jq - cx ^ q = (Jq - J ^ q) + (J ^ q - cx ^ q) := by ring
      rw [this, e2]
      refine Submodule.add_mem _ (hL _ n2) (Submodule.add_mem _ (hL _ ?_) (hR _ _ m2 ?_))
      · exact N.mul_mem_left _ (N.mul_mem_right _ (hqI N n1))
      · exact 𝔪.mul_mem_right _ m2
    conv_lhs => rw [hmax']
    rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl)
    exacts [hL _ n1, k2, k3]
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian 𝔪)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle) hNle

abbrev incl (A : ValuationSubring Qb) (K : IntermediateField ℚ Qb) : ↥(coeffSubring A K) →+* ↥A.toSubring :=
  Subring.inclusion inf_le_left

omit [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem modularEval_map_incl (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) A.toSubring (MvPolynomial.map (incl A K) r) = modularEval (1 * q) (coeffSubring A K) r := by
  unfold modularEval
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem pointEval_map_incl (b b' : k) (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    pointEval A.toSubring red b b' (MvPolynomial.map (incl A K) r) = pointEval (coeffSubring A K) (redRestrict red K) b b' r := by
  unfold pointEval
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

def kronPoly (S : Type*) [CommRing S] (R : Polynomial (Polynomial ℤ)) : MvPolynomial (Fin 2) S :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom S)) (MvPolynomial.X 0))
    (MvPolynomial.X 1) R

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem map_kronPoly {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (R : Polynomial (Polynomial ℤ)) :
    MvPolynomial.map f (kronPoly S R) = kronPoly T R := by
  unfold kronPoly
  rw [Polynomial.hom_eval₂, MvPolynomial.map_X]
  congr 1
  apply Polynomial.ringHom_ext
  · intro n
    simp only [map_intCast, eq_intCast]
  · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      MvPolynomial.map_X]

def genJ (q : ℕ) [Fact q.Prime] : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩
def genJq (q : ℕ) [Fact q.Prime] : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

omit [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem coe_genJ : ((genJ q : modularFunctionFieldBar (1 * q)) : LQ) = jqModC Qb := by
  show coeffMap (algebraMap ℚ Qb) (jqModC ℚ) = jqModC Qb
  exact map_jqModC _

omit [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem coe_genJq : ((genJq q : modularFunctionFieldBar (1 * q)) : LQ) = jqNModC Qb (1 * q) := by
  show coeffEmb Qb (qExpand ℚ (1 * q) jq) = qExpand Qb (1 * q) (jqModC Qb)
  rw [← coe_genJ (q := q)]
  show coeffEmb Qb (qExpand ℚ (1 * q) jq) = qExpand Qb (1 * q) (coeffEmb Qb jq)
  ext m
  unfold coeffEmb
  by_cases hm : ((1 * q : ℕ) : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hm
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ hm, qExpand_coeff_of_not_dvd _ _ hm, map_zero]

theorem stepDE_branch_product (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q) (h0 : a ≠ 0)
    (h1728 : a ≠ 1728) :
    ∃ U : ↥(R₀ q A red a K), IsUnit U ∧
      ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) * ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
        = ev q A red a K (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) * U := by
  classical
  obtain ⟨data, hKr⟩ := ModularCurve.exists_kroneckerCongruence_of_prime q

  set prodZ : Polynomial (Polynomial ℤ) :=
    (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) with hprodZ
  have hdvd : Polynomial.C (Polynomial.C (q : ℤ)) ∣ data.Φ - prodZ := by
    have hzero : reduceModBivar q (data.Φ - prodZ) = 0 := by
      rw [map_sub, hKr, sub_eq_zero]
      simp only [prodZ, reduceModBivar, map_mul, map_sub, map_pow, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.map_X]
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h := congrArg (fun P : Polynomial (Polynomial (ZMod q)) => (P.coeff n).coeff m) hzero
    simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero,
      eq_intCast] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h
  obtain ⟨R, hR'⟩ := hdvd
  have hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) +
      Polynomial.C (Polynomial.C (q : ℤ)) * R := by rw [← hR', hprodZ]; ring

  set Rp : MvPolynomial (Fin 2) ↥(coeffSubring A K) := kronPoly _ R with hRp
  have hmapR : MvPolynomial.map (incl A K) Rp = kronPoly (↥A.toSubring) R := map_kronPoly _ _
  have hevR : modularEval (1 * q) (coeffSubring A K) Rp = modularEval (1 * q) A.toSubring (kronPoly _ R) := by
    rw [← hmapR, modularEval_map_incl]
  have hα : modularEval (1 * q) (coeffSubring A K) Rp =
      (algebraMap Qb LQ (q : Qb))⁻¹ * ((((genJq q : modularFunctionFieldBar (1 * q)) : LQ) - ((genJ q : modularFunctionFieldBar (1 * q)) : LQ) ^ q) *
        (((genJ q : modularFunctionFieldBar (1 * q)) : LQ) - ((genJq q : modularFunctionFieldBar (1 * q)) : LQ) ^ q)) := by
    rw [hevR]
    exact ModularCurve.modularEval_kroneckerRemainder A data R hR
  rw [coe_genJ, coe_genJq] at hα

  have hpe : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) Rp =
      ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a := by
    rw [← pointEval_map_incl, hmapR]
    exact ModularCurve.pointEval_kroneckerRemainder red R a (a ^ q)
  have hne : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) Rp ≠ 0 := by
    rw [hpe]; exact kron_value_ne_zero red a ha ha2 hq h0 h1728 data R hR
  have hR0 : modularEval (1 * q) (coeffSubring A K) Rp ≠ 0 := fun h =>
    hne (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K Rp h)
  refine ⟨ev q A red a K Rp, ?_, ?_⟩
  · refine isUnit_iff_exists_inv.mpr ⟨⟨(modularEval (1 * q) (coeffSubring A K) Rp)⁻¹, 1, Rp, hne, ?_⟩, ?_⟩
    · rw [map_one]; exact inv_mul_cancel₀ hR0
    · exact Subtype.ext (mul_inv_cancel₀ hR0)
  · apply Subtype.ext
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) *
        modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) =
      modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) *
        modularEval (1 * q) (coeffSubring A K) Rp
    have e0 : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = jqModC Qb := by
      simp [modularEval]
    have e1 : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) = jqNModC Qb (1 * q) := by
      simp [modularEval]
    have eq' : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) =
        algebraMap Qb LQ (q : Qb) := by
      rw [map_natCast, map_natCast, map_natCast]
    have hq0 : algebraMap Qb LQ (q : Qb) ≠ 0 :=
      (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    rw [hα, map_sub, map_sub, map_pow, map_pow, e0, e1, eq', mul_inv_cancel_left₀ hq0]

theorem stepF_residue_surjective (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    [IsLocalRing ↥(R₀ q A red a K)] :
    Function.Surjective ((IsLocalRing.residue ↥(R₀ q A red a K)).comp (constHom q A red a K)) := by
  classical
  intro zbar
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective zbar
  obtain ⟨r, s, hs, hzs⟩ := (mem_modularLocalizedAtPoint _ _ _ _ _).mp z.2

  have hrange : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) p ∈ (redRestrict red K).range := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨c, (MvPolynomial.eval₂Hom_C _ _ c).symm⟩
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp =>
      rw [map_mul]; refine mul_mem hp ?_
      rw [pointEval, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact ⟨x, hx⟩
      · exact ⟨x ^ q, by rw [map_pow, hx]; rfl⟩
  obtain ⟨cr, hcr⟩ := hrange r
  obtain ⟨cs, hcs⟩ := hrange s
  have hcsU : IsUnit cs := (isUnit_coeffSubring_iff red K q cs).mpr (by rw [hcs]; exact hs)
  obtain ⟨u, rfl⟩ := hcsU
  have hured : redRestrict red K ↑u⁻¹ = (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s)⁻¹ := by
    rw [← hcs]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  obtain ⟨c, hc⟩ : ∃ c : ↥(coeffSubring A K), c = cr * ↑u⁻¹ := ⟨_, rfl⟩
  refine ⟨c, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff]
  intro hunit
  obtain ⟨y', hy'⟩ := hunit.exists_right_inv
  obtain ⟨r', s', hs', hys'⟩ := (mem_modularLocalizedAtPoint _ _ _ _ _).mp y'.2

  have h1 : (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) - (z : LQ)) * (y' : LQ) = 1 :=
    congrArg (fun w : ↥(R₀ q A red a K) => (w : LQ)) hy'

  have hrel : modularEval (1 * q) (coeffSubring A K) ((MvPolynomial.C c * s - r) * r' - s * s') = 0 := by
    simp only [map_sub, map_mul]
    rw [← hzs, ← hys']
    calc (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) * modularEval (1 * q) (coeffSubring A K) s - (z : LQ) * modularEval (1 * q) (coeffSubring A K) s) * ((y' : LQ) * modularEval (1 * q) (coeffSubring A K) s')
          - modularEval (1 * q) (coeffSubring A K) s * modularEval (1 * q) (coeffSubring A K) s'
        = ((modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) - (z : LQ)) * (y' : LQ)) * (modularEval (1 * q) (coeffSubring A K) s * modularEval (1 * q) (coeffSubring A K) s')
          - modularEval (1 * q) (coeffSubring A K) s * modularEval (1 * q) (coeffSubring A K) s' := by ring
      _ = 0 := by rw [h1, one_mul, sub_self]
  have hker := ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K _ hrel
  have hpeC : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r * (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s)⁻¹ := by
    rw [show pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) = redRestrict red K c from MvPolynomial.eval₂Hom_C _ _ _,
      hc, map_mul, hcr, hured]
  have h' : (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) * pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s - pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r) * pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r' - pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s * pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s' = 0 := by
    simpa only [map_sub, map_mul] using hker
  rw [hpeC, inv_mul_cancel_right₀ hs, sub_self, zero_mul, zero_sub, neg_eq_zero] at h'
  exact mul_ne_zero hs hs' h'

end Steps

section MainC01
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem irreducible_and_natCast_eq_of_uniformizer (red : A →+* k) (K : IntermediateField ℚ Qb)
    [FiniteDimensional ℚ K] (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    Irreducible ϖ ∧ ∃ (e : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ e ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ e * ε := by
  classical
  haveI := stepA_dvr red K q
  have hmax : maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := by
    ext c
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton,
      isUnit_coeffSubring_iff red K q c, not_not, hϖ c]
    exact Iff.rfl
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  refine ⟨hirr, ?_⟩
  have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h
    push_cast at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hirr
  refine ⟨n, u, ?_, u.isUnit, by rw [hn, mul_comm]⟩
  by_contra hlt
  have hn0 : n = 0 := by omega
  rw [hn0, pow_zero, mul_one] at hn
  have hu : IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := hn ▸ u.isUnit
  exact ((isUnit_coeffSubring_iff red K q _).mp hu) (by rw [map_natCast, CharP.cast_eq_zero])

theorem jWidth_eq_one_of_ne (a : k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) : jWidth a = 1 := by
  simp [jWidth, h0, h1728]

theorem _root_.P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728.solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : 5 ≤ q) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) :
    ∃ (eK : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      IsUnit w ∧
      G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w ∧
      (∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'}) ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime ∧
      (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime ∧
      H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} ∧
      G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} ∧
      Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
  classical
  obtain ⟨hϖirr, e, ε, he, hε, hqe⟩ := irreducible_and_natCast_eq_of_uniformizer (q := q) red K ϖ hϖ
  obtain ⟨hnoeth, hloc, hdim, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hnoeth; haveI := hloc
  obtain ⟨⟨hPG, hHG, -⟩, hbr2⟩ :=
    ModularCurve.NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint red a K ϖ hϖ
  obtain ⟨hPH, hGH⟩ := hbr2 ha2
  obtain ⟨U, hU, hGHU⟩ := stepDE_branch_product red a K ha ha2 hq h0 h1728
  have hjw : jWidth a = 1 := jWidth_eq_one_of_ne a h0 h1728
  have halg : ∀ c, constHom q A red a K c = ev q A red a K (MvPolynomial.C c) := fun c => rfl
  refine ⟨e, ε, he, hε, hqe,
    ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
    ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
    ev q A red a K (MvPolynomial.C ε) * U,
    (hε.map (constHom q A red a K)).mul hU, ?_, ?_, hPG, hPH, hHG, hGH, rfl, rfl⟩
  ·
    rw [show jWidth a * e = e by rw [hjw, one_mul], hGHU, hqe]
    change evHom q A red a K (MvPolynomial.C (ϖ ^ e * ε)) * U =
      evHom q A red a K (MvPolynomial.C ϖ) ^ e * (evHom q A red a K (MvPolynomial.C ε) * U)
    rw [map_mul, map_mul, map_pow, map_pow]
    ring
  ·
    intro inst
    have h := stepC_maximalIdeal_eq red a K ha2 ϖ hϖ x hx hmax
    convert h using 2

end MainC01

end ChartKAssembly
end ModularCurve

end

end S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
end P2MW
export P2MW.S_ModularCurve_exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728 (solution)
