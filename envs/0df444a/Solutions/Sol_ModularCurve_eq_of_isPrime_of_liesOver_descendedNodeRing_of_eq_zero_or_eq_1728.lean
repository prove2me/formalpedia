-- Prove2me | solution 1 for ModularCurve.eq_of_isPrime_of_liesOver_descendedNodeRing_of_eq_zero_or_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ceaa3e0b-7295-5276-8c94-bb96d80f1b29

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_Subring_eq_of_isMaximal_of_marked_galois_descent
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_forall_lambdaEval_mem_of_isMaximal
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_eq_of_isPrime_of_forall_lambdaEval_mem
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver
import Theorems.Thm_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_of_isPrime_of_liesOver_descendedNodeRing_of_eq_zero_or_eq_1728
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_eq_of_isPrime_of_liesOver_descendedNodeRing_of_eq_zero_or_eq_1728.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap ssJSet NodeLocalized.exists_mul_eq_of_mem_fieldOver NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing qExpand_two_jq_mul_lambdaModC_sq LambdaNodeLocalized.exists_forall_lambdaEval_mem_of_isMaximal LambdaNodeLocalized.eq_of_isPrime_of_forall_lambdaEval_mem LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem LambdaNodeLocalized.qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver"
p2m_open "ModularCurve"
namespace ChartKDeg5Assembly

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

section FieldFacts
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

theorem const_mem_fieldOver (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) c ∈ fieldOver (1 * q) K :=
  Subfield.subset_closure (Or.inl ⟨⟨(c : Qb), c.2.2⟩, rfl⟩)

theorem const_mem_lambdaFieldOver (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) c ∈ lambdaFieldOver q K :=
  Subfield.subset_closure (Or.inl ⟨⟨(c : Qb), c.2.2⟩, rfl⟩)

theorem modularEval_mem_fieldOver (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ fieldOver (1 * q) K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact const_mem_fieldOver q A K c
  | add p p' hp hp' => rw [map_add]; exact add_mem hp hp'
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    fin_cases i
    · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
    · exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem lambdaEval_mem_lambdaFieldOver (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    lambdaEval q (coeffSubring A K) p ∈ lambdaFieldOver q K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact const_mem_lambdaFieldOver q A K c
  | add p p' hp hp' => rw [map_add]; exact add_mem hp hp'
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    fin_cases i
    · exact lambdaModC_mem_lambdaFieldOver q K
    · exact lambdaNModC_mem_lambdaFieldOver q K

theorem R₀_le_fieldOver [CharP k q] : R₀ q A red a K ≤ (fieldOver (1 * q) K).toSubring := by
  rintro f ⟨r, s, hs, hfs⟩
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := fun h0 =>
    hs (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s h0)
  have : f = modularEval (1 * q) (coeffSubring A K) r / modularEval (1 * q) (coeffSubring A K) s := by
    rw [eq_div_iff hs0, hfs]
  rw [Subfield.mem_toSubring, this]
  exact div_mem (modularEval_mem_fieldOver q A K r) (modularEval_mem_fieldOver q A K s)

omit [Fact q.Prime] in

theorem qExpand_algebraMap (N : ℕ) [NeZero N] (c : Qb) :
    qExpand Qb N (algebraMap Qb LQ c) = algebraMap Qb LQ c := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

omit [Fact q.Prime] in

theorem jLambda_Qb :
    qExpand Qb 2 (jqModC Qb) * lambdaModC Qb ^ 2 * (16 * lambdaModC Qb - 1) ^ 2
      = (256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1) ^ 3 := by
  have h := congrArg (laurentMap (algebraMap ℚ Qb)) ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
  have hj : laurentMap (algebraMap ℚ Qb) jq = jqModC Qb := by
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ Qb)
  have hμ : laurentMap (algebraMap ℚ Qb) (lambdaModC ℚ) = lambdaModC Qb := by
    rw [lambdaModC, lambdaModC, laurentMap_laurentMap]
    exact congrArg (fun g => laurentMap g lambdaInt) (RingHom.ext_int _ _)
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, laurentMap_qExpand, hj, hμ, map_ofNat] using h

theorem jLambda_Qb_q :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) (jLambda_Qb)
  have hj : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    rw [jqNModC, qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hj, lambdaNModC] using h

end FieldFacts

section Integral
variable (q : ℕ) [Fact q.Prime] (A : ValuationSubring Qb) {k : Type*} [Field k] [CharP k q]
  (K : IntermediateField ℚ Qb)

theorem inv_two_pow_mem (red : A →+* k) (hq : 5 ≤ q) (n : ℕ) : ((2 : Qb) ^ n)⁻¹ ∈ coeffSubring A K := by
  have h : IsUnit (((2 ^ n : ℕ) : ↥(coeffSubring A K))) := by
    rw [isUnit_coeffSubring_iff red K q, map_natCast, Ne, CharP.cast_eq_zero_iff k q]
    intro hdvd
    have h2 : q ∣ 2 := (Fact.out : q.Prime).dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨u, hu⟩ := h
  have hmul : (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) * (2 : Qb) ^ n = 1 := by
    have h1 := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) u.inv_mul
    rw [hu] at h1
    first | simpa using h1 | (push_cast at h1 ⊢; exact h1) | (norm_num at h1 ⊢; exact h1)
  have : ((2 : Qb) ^ n)⁻¹ = (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  rw [this]; exact SetLike.coe_mem _

omit [CharP k q] in
theorem ev_C_coe (red : A →+* k) (a : k) (c : ↥(coeffSubring A K)) :
    ((ev q A red a K (MvPolynomial.C c) : ↥(R₀ q A red a K)) : LQ) = algebraMap Qb LQ (c : Qb) := by
  show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) = _
  rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; rfl

theorem isIntegralElem_sixteen_mul (red : A →+* k) (a : k) (hq : 5 ≤ q)
    (J : ↥(R₀ q A red a K)) (m : LQ)
    (hJ : qExpand Qb 2 (J : LQ) * m ^ 2 * (16 * m - 1) ^ 2 = (256 * m ^ 2 - 16 * m + 1) ^ 3) :
    ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem (16 * m) := by
  set f := (qExpand Qb 2).comp (R₀ q A red a K).subtype with hf
  have h256mem : (256 : Qb)⁻¹ ∈ coeffSubring A K := by
    have := inv_two_pow_mem q A K red hq 8; norm_num at this; rwa [one_div] at this
  let c : ↥(R₀ q A red a K) := ev q A red a K (MvPolynomial.C ⟨(256 : Qb)⁻¹, h256mem⟩) * J
  have hc : f c = algebraMap Qb LQ (256 : Qb)⁻¹ * qExpand Qb 2 (J : LQ) := by
    rw [hf, RingHom.comp_apply, Subring.subtype_apply, Subring.coe_mul, map_mul, ev_C_coe, qExpand_algebraMap]
  have h256 : algebraMap Qb LQ (256 : Qb)⁻¹ * 256 = 1 := by
    rw [← map_ofNat (algebraMap Qb LQ) 256, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  open Polynomial in
  refine ⟨(X ^ 2 - X + 1) ^ 3 - C c * (X ^ 2 * (X - 1) ^ 2), by monicity!, ?_⟩
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one, hc]
  linear_combination (-1 : LQ) * hJ - (qExpand Qb 2 (J : LQ) * m ^ 2 * (16 * m - 1) ^ 2) * h256

theorem isIntegralElem_of_jRel (red : A →+* k) (a : k) (hq : 5 ≤ q)
    (J : ↥(R₀ q A red a K)) (m : LQ)
    (hJ : qExpand Qb 2 (J : LQ) * m ^ 2 * (16 * m - 1) ^ 2 = (256 * m ^ 2 - 16 * m + 1) ^ 3) :
    ((qExpand Qb 2).comp (R₀ q A red a K).subtype).IsIntegralElem m := by
  have h16mem : (16 : Qb)⁻¹ ∈ coeffSubring A K := by
    have := inv_two_pow_mem q A K red hq 4; norm_num at this; rwa [one_div] at this
  refine RingHom.IsIntegralElem.of_mul_unit _ m 16 (ev q A red a K (MvPolynomial.C ⟨(16 : Qb)⁻¹, h16mem⟩)) ?_ ?_
  · rw [RingHom.comp_apply, Subring.subtype_apply, ev_C_coe, qExpand_algebraMap,
      ← map_ofNat (algebraMap Qb LQ) 16, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  · rw [mul_comm]; exact isIntegralElem_sixteen_mul q A K red a hq J m hJ

end Integral

section Main

theorem _root_.P2MW.S_ModularCurve_eq_of_isPrime_of_liesOver_descendedNodeRing_of_eq_zero_or_eq_1728.solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hq : 5 ≤ q) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a)
    (hl : ∀ l : k, l ^ (q ^ 2) = l → a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 →
      ∃ y : ↥(coeffSubring A K), redRestrict red K y = l)
    (B : Subring (LaurentSeries (AlgebraicClosure ℚ)))
    (hBF : B ≤ (fieldOver (1 * q) K).toSubring)
    (hNB : modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ≤ B)
    (hint : ∀ x ∈ B, IsIntegral ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) x)
    (P₁ P₂ : Ideal ↥B) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : ∀ r : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 →
      (⟨modularEval (1 * q) (coeffSubring A K) r,
        hNB (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r)⟩ : ↥B) ∈ P₁)
    (h₂ : ∀ r : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 →
      (⟨modularEval (1 * q) (coeffSubring A K) r,
        hNB (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r)⟩ : ↥B) ∈ P₂) :
    P₁ = P₂ := by
  classical
  obtain ⟨x, hx'⟩ := hx

  obtain ⟨ϖ, -, hϖ, -⟩ := stepA_uniformizer red K q
  obtain ⟨-, hloc, -, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx' ϖ hϖ
  haveI := hloc
  letI algRB : Algebra ↥(R₀ q A red a K) ↥B := (Subring.inclusion hNB).toAlgebra
  have halgRB : ∀ r : ↥(R₀ q A red a K), (algebraMap ↥(R₀ q A red a K) ↥B r : LQ) = (r : LQ) := fun r => rfl
  let Bval : ↥B →ₐ[↥(R₀ q A red a K)] LQ :=
    { B.subtype with commutes' := fun r => rfl }
  haveI : Algebra.IsIntegral ↥(R₀ q A red a K) ↥B :=
    ⟨fun b => (isIntegral_algHom_iff Bval Subtype.val_injective).mp (hint b b.2)⟩
  have hPmax : ∀ (P : Ideal ↥B) [P.IsPrime],
      (∀ r : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 →
        (⟨modularEval (1 * q) (coeffSubring A K) r,
          hNB (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r)⟩ : ↥B)
          ∈ P) → P.IsMaximal := by
    intro P _ hP
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ↥(R₀ q A red a K))
    have hle : IsLocalRing.maximalIdeal ↥(R₀ q A red a K) ≤ P.comap (algebraMap ↥(R₀ q A red a K) ↥B) := by
      rw [hmax, Ideal.span_le]
      rintro _ (rfl | rfl | rfl)
      · exact hP _ (by
          rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
          exact (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩)
      · exact hP _ (by simp [pointEval, hx'])
      · exact hP _ (by simp [pointEval, hx', map_pow])
    have hne : P.comap (algebraMap ↥(R₀ q A red a K) ↥B) ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
    rw [← (IsLocalRing.maximalIdeal.isMaximal ↥(R₀ q A red a K)).eq_of_le hne hle]
    exact IsLocalRing.maximalIdeal.isMaximal _
  haveI := hPmax P₁ h₁
  haveI := hPmax P₂ h₂

  have hl' : ∀ l : k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 →
      ∃ y : ↥(coeffSubring A K), redRestrict red K y = l := fun l h =>
    hl l (pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq a h01728 l h) h
  have hF : ∀ l : k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 →
      l ^ (q ^ 2) = l := fun l h => pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 hq a h01728 l h
  let ι : Type := {y : ↥(coeffSubring A K) //
    a * ((16 * redRestrict red K y) ^ 2 * (16 * redRestrict red K y - 1) ^ 2)
      = 256 * ((16 * redRestrict red K y) ^ 2 - 16 * redRestrict red K y + 1) ^ 3 ∧
    redRestrict red K y ^ (q ^ 2) = redRestrict red K y}
  let G : ι → Set LQ := fun i => {g | ∃ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
    pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K i.1) (redRestrict red K i.1 ^ q) p = 0 ∧
      lambdaEval q (coeffSubring A K) p = g}
  let T : Subring LQ := (lambdaEval q (coeffSubring A K)).range
  have hGT : ∀ i, G i ⊆ T := by
    rintro i g ⟨p, -, rfl⟩; exact ⟨p, rfl⟩
  have hjX0 : ((ev q A red a K (MvPolynomial.X 0) : ↥(R₀ q A red a K)) : LQ) = jqModC Qb := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = _
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hjX1 : ((ev q A red a K (MvPolynomial.X 1) : ↥(R₀ q A red a K)) : LQ) = jqNModC Qb (1 * q) := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1) = _
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl

  refine Subring.eq_of_isMaximal_of_marked_galois_descent (R₀ q A red a K) (fieldOver (1 * q) K)
    (lambdaFieldOver q K) (qExpand Qb 2) (R₀_le_fieldOver q A red a K)
    (fun z hz => ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver red a K hz)
    (fun z hz => ModularCurve.LambdaNodeLocalized.qExpand_two_mem_lambdaFieldOver_of_mem_fieldOver q K hz)
    {lambdaModC Qb, lambdaNModC Qb q} ((Set.finite_singleton _).insert _)
    (Set.insert_subset (lambdaModC_mem_lambdaFieldOver q K)
      (Set.singleton_subset_iff.mpr (lambdaNModC_mem_lambdaFieldOver q K))) ?_ ?_ T ?_ ?_ G hGT ?_ ?_ ?_
    B hNB hBF hint P₁ P₂
  ·
    rintro s (rfl | rfl)
    · exact isIntegralElem_of_jRel q A K red a hq (ev q A red a K (MvPolynomial.X 0)) _ (by rw [hjX0]; exact jLambda_Qb)
    · exact isIntegralElem_of_jRel q A K red a hq (ev q A red a K (MvPolynomial.X 1)) _
        (by rw [hjX1]; exact jLambda_Qb_q q)
  ·
    show Subfield.closure _ ≤ _
    rw [Subfield.closure_le]
    rintro z (⟨c, rfl⟩ | rfl | rfl)
    · refine Subfield.subset_closure (Or.inl ?_)
      refine ⟨CharPReduction.constSeries K.toSubalgebra.toSubring c,
        Subfield.subset_closure (Or.inl ⟨c, rfl⟩), ?_⟩
      exact qExpand_algebraMap 2 _
    · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
    · exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  ·
    rintro _ ⟨p, rfl⟩
    exact lambdaEval_mem_lambdaFieldOver q A K p
  ·
    rintro _ ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine Subring.subset_closure (Or.inl ⟨ev q A red a K (MvPolynomial.C c), (ev q A red a K _).2, ?_⟩)
      show qExpand Qb 2 (modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c)) = lambdaEval q (coeffSubring A K) (MvPolynomial.C c)
      rw [modularEval, lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
      exact qExpand_algebraMap 2 _
    | add p p' hp hp' => rw [map_add]; exact add_mem hp hp'
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subring.subset_closure (Or.inr ?_))
      rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  ·
    intro B' hBL hRB' hTB hint' N hN
    haveI := hN
    obtain ⟨l, hrel, hmark⟩ := ModularCurve.LambdaNodeLocalized.exists_forall_lambdaEval_mem_of_isMaximal hq red a K
      ⟨x, hx'⟩ hl' hF B' hBL hRB' (fun p => hTB ⟨p, rfl⟩) hint' N
    obtain ⟨y, hy⟩ := hl' l hrel
    refine ⟨⟨y, by rw [hy]; exact hrel, by rw [hy]; exact hF l hrel⟩, ?_⟩
    rintro g ⟨p, hp, rfl⟩
    have hp' : pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) p = 0 := by rw [← hy]; exact hp
    exact hmark p hp'
  ·
    intro i B' hBL hRB' hTB hint' Q₁ Q₂ hQ₁ hQ₂ hm₁ hm₂
    haveI := hQ₁; haveI := hQ₂
    exact ModularCurve.LambdaNodeLocalized.eq_of_isPrime_of_forall_lambdaEval_mem hq red a ha K i.1 i.2.2 i.2.1
      B' hBL hRB' (fun p => hTB ⟨p, rfl⟩) hint' Q₁ Q₂
      (fun p hp => hm₁ _ ⟨p, hp, rfl⟩) (fun p hp => hm₂ _ ⟨p, hp, rfl⟩)
  ·
    intro i j
    obtain ⟨σ, hfix, htr⟩ :=
      ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem hq red a h01728 K
        i.1 j.1 i.2.1 j.2.1
    refine ⟨σ, hfix, ?_⟩
    intro B' hBL hTB hσB I hI g hg
    obtain ⟨p, hp, rfl⟩ := hg
    exact htr B' hBL (fun p => hTB ⟨p, rfl⟩) hσB I (fun p hp => hI _ ⟨p, hp, rfl⟩) p hp

end Main

end ChartKDeg5Assembly
end ModularCurve

end

end S_ModularCurve_eq_of_isPrime_of_liesOver_descendedNodeRing_of_eq_zero_or_eq_1728
end P2MW
export P2MW.S_ModularCurve_eq_of_isPrime_of_liesOver_descendedNodeRing_of_eq_zero_or_eq_1728 (solution)
