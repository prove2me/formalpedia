-- Prove2me | solution 1 for ModularCurve.isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/72e7c024-cfed-53ec-bc55-88095d58bc07

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Theorems.Thm_ModularCurve_lambdaEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_pointEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Theorems.Thm_ModularCurve_exists_lambdaKroneckerCongruence
import Theorems.Thm_ModularCurve_existsUnique_lambdaKroneckerRemainder
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring.ModularCurve"
open ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "lambdaModC lambdaNModC ssJSet LambdaModularPolynomialData lambdaEval_kroneckerRemainder pointEval_kroneckerRemainder eval_lambdaKroneckerRemainder_ne_zero LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two exists_lambdaKroneckerCongruence existsUnique_lambdaKroneckerRemainder NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing mem_ssJSet_algebraMap_of_pow_eq_of_ne_two LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint"
p2m_open "ModularCurve"
namespace ChartLambdaAssembly

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Defs
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

abbrev R₀ : Subring LQ :=
  lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) a (a ^ q)

abbrev ev (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) : ↥(R₀ q A red a K) :=
  ⟨lambdaEval q (coeffSubring A K) p,
    lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) a (a ^ q) p⟩

def evHom : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(R₀ q A red a K) :=
  (lambdaEval q (coeffSubring A K)).codRestrict (R₀ q A red a K)
    (lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) a (a ^ q))

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

theorem jval_pow_eq {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] (hq2 : q ≠ 2)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1) (a : k)
    (haeq : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    a ^ (q ^ 2) = a := by
  set φ : k →+* k := iterateFrobenius k q 2 with hφ
  have hφl : φ l = l := by rw [hφ, iterateFrobenius_def, hl2]
  have hφa : φ a = a ^ (q ^ 2) := by rw [hφ, iterateFrobenius_def]
  have h := congrArg φ haeq
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, map_one, hφl, hφa] at h
  have h16 : (16 : k) ≠ 0 := by
    rw [show (16 : k) = ((16 : ℕ) : k) by norm_cast, Ne, CharP.cast_eq_zero_iff k q]
    intro hdvd
    have h2 : q ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (Fact.out : q.Prime) (show q ∣ 2 ^ 4 by simpa using hdvd))
    have := Nat.le_of_dvd (by norm_num) h2
    have := (Fact.out : q.Prime).two_le
    omega
  have hD : ((16 * l) ^ 2 * (16 * l - 1) ^ 2 : k) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero h16 hl0)) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  have : (a ^ (q ^ 2) - a) * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 0 := by rw [sub_mul, h, haeq, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)

theorem kron_value_ne_zero {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]
    [DecidableEq k] (red : A →+* k) (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hss : ∃ a ∈ ssJSet q k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (hq : 5 ≤ q) (data : LambdaModularPolynomialData q) (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) +
      Polynomial.C (Polynomial.C (q : ℤ)) * R) :
    ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (l ^ q))).eval l ≠ 0 := by
  classical
  have hq2 : q ≠ 2 := by omega
  let k' := AlgebraicClosure k
  let ι : k →+* k' := algebraMap k k'
  haveI : CharP k' q := charP_of_injective_algebraMap ι.injective q
  have hk : ∀ y : k', (∃ n : ℕ, 0 < n ∧ y ^ (q ^ n) = y) → y ∈ (algebraMap k k').range :=
    fun y hy => mem_range_of_pow_eq red ι y hy
  obtain ⟨a, ha, haeq⟩ := hss
  have ha2 : a ^ (q ^ 2) = a := jval_pow_eq hq2 l hl2 hl0 hl1 a haeq
  have ha' : algebraMap k k' a ∈ ssJSet q k' := ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_two hq2 hk a ha ha2
  have hl0' : ι l ≠ 0 := (map_ne_zero ι).mpr hl0
  have hl1' : 16 * ι l ≠ 1 := by
    intro h
    apply hl1
    apply ι.injective
    rw [map_mul, map_ofNat, map_one]; exact h
  have hss' : ∃ a' ∈ ssJSet q k', a' * ((16 * ι l) ^ 2 * (16 * ι l - 1) ^ 2) = 256 * ((16 * ι l) ^ 2 - 16 * ι l + 1) ^ 3 := by
    refine ⟨ι a, ha', ?_⟩
    have h := congrArg ι haeq
    simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, map_one] at h
    exact h
  have hK2 := ModularCurve.eval_lambdaKroneckerRemainder_ne_zero hq data R hR (ι l) hl0' hl1' hss'
  intro hval
  apply hK2

  set P := R.map (Polynomial.mapRingHom (Int.castRingHom k)) with hP
  have hcast : Int.castRingHom k' = ι.comp (Int.castRingHom k) := RingHom.ext_int _ _
  have hmap : R.map (Polynomial.mapRingHom (Int.castRingHom k')) = P.map (Polynomial.mapRingHom ι) := by
    rw [hcast, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map]
  rw [hmap, ← map_pow, show Polynomial.C (ι (l ^ q)) = Polynomial.mapRingHom ι (Polynomial.C (l ^ q)) by
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
theorem lambdaEval_map_incl (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    lambdaEval q A.toSubring (MvPolynomial.map (incl A K) r) = lambdaEval q (coeffSubring A K) r := by
  unfold lambdaEval
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

theorem stepDE_branch_product (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1 : 16 * a ≠ 1)
    (hss : ∃ j ∈ ssJSet q k, j * ((16 * a) ^ 2 * (16 * a - 1) ^ 2) = 256 * ((16 * a) ^ 2 - 16 * a + 1) ^ 3) (hq : 5 ≤ q) :
    ∃ U : ↥(R₀ q A red a K), IsUnit U ∧
      ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) * ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
        = ev q A red a K (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) * U := by
  classical
  have hq2 : q ≠ 2 := by omega
  obtain ⟨data, hKr⟩ := ModularCurve.exists_lambdaKroneckerCongruence q hq2

  obtain ⟨R, hR, -⟩ := ModularCurve.existsUnique_lambdaKroneckerRemainder q data hKr

  set Rp : MvPolynomial (Fin 2) ↥(coeffSubring A K) := kronPoly _ R with hRp
  have hmapR : MvPolynomial.map (incl A K) Rp = kronPoly (↥A.toSubring) R := map_kronPoly _ _
  have hevR : lambdaEval q (coeffSubring A K) Rp = lambdaEval q A.toSubring (kronPoly _ R) := by
    rw [← hmapR, lambdaEval_map_incl]
  have hα : lambdaEval q (coeffSubring A K) Rp =
      (algebraMap Qb LQ (q : Qb))⁻¹ * ((lambdaNModC Qb q - lambdaModC Qb ^ q) * (lambdaModC Qb - lambdaNModC Qb q ^ q)) := by
    rw [hevR]
    exact ModularCurve.lambdaEval_kroneckerRemainder data R hR A.toSubring

  have hpe : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) Rp =
      ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a := by
    rw [← pointEval_map_incl, hmapR]
    exact ModularCurve.pointEval_kroneckerRemainder red R a (a ^ q)
  have hne : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) Rp ≠ 0 := by
    rw [hpe]; exact kron_value_ne_zero red a ha2 h0 h1 hss hq data R hR
  have hR0 : lambdaEval q (coeffSubring A K) Rp ≠ 0 := fun h =>
    hne (ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red a ha2 K Rp h)
  refine ⟨ev q A red a K Rp, ?_, ?_⟩
  · refine isUnit_iff_exists_inv.mpr ⟨⟨(lambdaEval q (coeffSubring A K) Rp)⁻¹, 1, Rp, hne, ?_⟩, ?_⟩
    · rw [map_one]; exact inv_mul_cancel₀ hR0
    · exact Subtype.ext (mul_inv_cancel₀ hR0)
  · apply Subtype.ext
    show lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) *
        lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) =
      lambdaEval q (coeffSubring A K) (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) *
        lambdaEval q (coeffSubring A K) Rp
    have e0 : lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) = lambdaModC Qb := by
      simp [lambdaEval]
    have e1 : lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) = lambdaNModC Qb q := by
      simp [lambdaEval]
    have eq' : lambdaEval q (coeffSubring A K) (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) =
        algebraMap Qb LQ (q : Qb) := by
      rw [map_natCast, map_natCast, map_natCast]
    have hq0 : algebraMap Qb LQ (q : Qb) ≠ 0 :=
      (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    rw [hα, map_sub, map_sub, map_pow, map_pow, e0, e1, eq', mul_inv_cancel_left₀ hq0]

theorem stepF_residue_surjective (hq2 : q ≠ 2) (ha2 : a ^ (q ^ 2) = a) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    [IsLocalRing ↥(R₀ q A red a K)] :
    Function.Surjective ((IsLocalRing.residue ↥(R₀ q A red a K)).comp (constHom q A red a K)) := by
  classical
  intro zbar
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective zbar
  obtain ⟨r, s, hs, hzs⟩ := (mem_lambdaLocalizedAtPoint _ _ _ _ _).mp z.2

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
  obtain ⟨r', s', hs', hys'⟩ := (mem_lambdaLocalizedAtPoint _ _ _ _ _).mp y'.2

  have h1 : (lambdaEval q (coeffSubring A K) (MvPolynomial.C c) - (z : LQ)) * (y' : LQ) = 1 :=
    congrArg (fun w : ↥(R₀ q A red a K) => (w : LQ)) hy'

  have hrel : lambdaEval q (coeffSubring A K) ((MvPolynomial.C c * s - r) * r' - s * s') = 0 := by
    simp only [map_sub, map_mul]
    rw [← hzs, ← hys']
    calc (lambdaEval q (coeffSubring A K) (MvPolynomial.C c) * lambdaEval q (coeffSubring A K) s - (z : LQ) * lambdaEval q (coeffSubring A K) s) * ((y' : LQ) * lambdaEval q (coeffSubring A K) s')
          - lambdaEval q (coeffSubring A K) s * lambdaEval q (coeffSubring A K) s'
        = ((lambdaEval q (coeffSubring A K) (MvPolynomial.C c) - (z : LQ)) * (y' : LQ)) * (lambdaEval q (coeffSubring A K) s * lambdaEval q (coeffSubring A K) s')
          - lambdaEval q (coeffSubring A K) s * lambdaEval q (coeffSubring A K) s' := by ring
      _ = 0 := by rw [h1, one_mul, sub_self]
  have hker := ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red a ha2 K _ hrel
  have hpeC : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r * (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s)⁻¹ := by
    rw [show pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) = redRestrict red K c from MvPolynomial.eval₂Hom_C _ _ _,
      hc, map_mul, hcr, hured]
  have h' : (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (MvPolynomial.C c) * pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s - pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r) * pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r' - pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s * pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s' = 0 := by
    simpa only [map_sub, map_mul] using hker
  rw [hpeC, inv_mul_cancel_right₀ hs, sub_self, zero_mul, zero_sub, neg_eq_zero] at h'
  exact mul_ne_zero hs hs' h'

end Steps

section Main
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem stepG_isIntegrallyClosed (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1 : 16 * a ≠ 1)
    (hss : ∃ j ∈ ssJSet q k, j * ((16 * a) ^ 2 * (16 * a - 1) ^ 2) = 256 * ((16 * a) ^ 2 - 16 * a + 1) ^ 3) (hq : 5 ≤ q)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K] (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a) :
    IsIntegrallyClosed ↥(R₀ q A red a K) := by
  classical
  have hq2 : q ≠ 2 := by omega
  obtain ⟨x, hx⟩ := hx
  obtain ⟨ϖ, hϖirr, hϖ, e, ε, he, hε, hqe⟩ := stepA_uniformizer red K q
  obtain ⟨hnoeth, hloc, hdim, hmax⟩ :=
    ModularCurve.LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring hq2 red a ha2 K x hx ϖ hϖ
  haveI := hnoeth; haveI := hloc
  obtain ⟨⟨hPG, hHG, -⟩, hbr2⟩ :=
    ModularCurve.LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint hq2 red a ha2 K ϖ hϖ
  obtain ⟨hPH, hGH⟩ := hbr2 ha2
  obtain ⟨U, hU, hGHU⟩ := stepDE_branch_product red a K ha2 h0 h1 hss hq
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := stepA_dvr red K q
  letI : Algebra ↥(coeffSubring A K) ↥(R₀ q A red a K) := (constHom q A red a K).toAlgebra
  have halg : ∀ c, algebraMap ↥(coeffSubring A K) ↥(R₀ q A red a K) c = ev q A red a K (MvPolynomial.C c) :=
    fun c => rfl
  have h2 : IsUnit (2 : ↥(R₀ q A red a K)) := by
    have h2A : IsUnit (2 : ↥(coeffSubring A K)) := by
      rw [isUnit_coeffSubring_iff red K q]
      rw [show (2 : ↥(coeffSubring A K)) = ((2 : ℕ) : ↥(coeffSubring A K)) by norm_cast, map_natCast]
      rw [Ne, CharP.cast_eq_zero_iff k q]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have := h2A.map (constHom q A red a K)
    rwa [map_ofNat] at this
  refine IsLocalRing.isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_unit ϖ hϖirr
    (stepF_residue_surjective red a K hq2 ha2 x hx)
    (ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)) (ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q))
    (ev q A red a K (MvPolynomial.C ε) * U) ((hε.map (constHom q A red a K)).mul hU) e he ?_ ?_ ?_ ?_ hHG hGH h2
  · rw [hGHU, halg, ← evHom_apply, ← evHom_apply, ← evHom_apply, hqe, map_mul, map_pow, map_mul, map_pow]
    ring
  · rw [halg]; exact stepC_maximalIdeal_eq red a K ha2 ϖ hϖ x hx hmax
  · rw [halg]; exact hPG
  · rw [halg]; exact hPH

end Main

end ChartLambdaAssembly
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring.ModularCurve ModularCurve.ChartLambdaAssembly in

theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hss : ∃ a ∈ ssJSet q k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = l) :
    IsIntegrallyClosed ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) :=
  stepG_isIntegrallyClosed red l hl2 hl0 hl1 hss hq K hx

end

end S_ModularCurve_isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring
end P2MW
export P2MW.S_ModularCurve_isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring (solution)
