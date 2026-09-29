-- Prove2me | solution 1 for ModularCurve.exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a1495508-6bfb-539d-8b5c-1b65af685641

import Mathlib
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_SupersingularNodes
import Theorems.Thm_ModularCurve_frobenius_identity_geom_unconditional
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_modularFunctionFieldC_self_collapse_unconditional
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_algebraMap_residueField_charLGeomPlaceOfPoint_surjective
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ModularCurve_exists_numberField_presentation
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve AlgebraicCurve Polynomial"

section ChartKFromIC
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full NodeLocalized.modularEval NodeLocalized.pointEval NodeLocalized.modularLocalizedAtPoint NodeLocalized.modularEval_mem_modularLocalizedAtPoint ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar coe_geomAut_coeffEmb frobNodePair frobenius_identity_geom_unconditional exists_isFrickeAutFull CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint ssJSet algebraMap_residueField_charLGeomPlaceOfPoint_surjective exists_numberField_presentation isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
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

section MainFromIC
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem chartK_of_isIntegrallyClosed (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a)
    (hic : IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
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

  have hBR : B ≤ R₀ q A red a K := fun x hxB =>
    stepI_mem_of_isIntegral q A red a K hic (hBF hxB) (hint x hxB)
  have hB : B = R₀ q A red a K := le_antisymm hBR hNB
  subst hB

  obtain ⟨x, hx⟩ := hx
  obtain ⟨ϖ, -, hϖ, -⟩ := stepA_uniformizer red K q
  obtain ⟨hnoeth, hloc, -, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hloc
  have hm : maximalIdeal ↥(R₀ q A red a K) = _ := hmax
  have hgen : ∀ (P : Ideal ↥(R₀ q A red a K)), (∀ r : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 → ev q A red a K r ∈ P) →
      maximalIdeal ↥(R₀ q A red a K) ≤ P := by
    intro P hP
    rw [hm, Ideal.span_le]
    rintro _ (rfl | rfl | rfl)
    · exact hP _ (by rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; exact (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩)
    · exact hP _ (by simp [pointEval, hx])
    · exact hP _ (by simp [pointEval, hx, map_pow])
  have key : ∀ (P : Ideal ↥(R₀ q A red a K)) [P.IsPrime], (∀ r : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 → ev q A red a K r ∈ P) →
      P = maximalIdeal ↥(R₀ q A red a K) := fun P _ hP =>
    le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) (hgen P hP)
  rw [key P₁ (fun r hr => h₁ r hr), key P₂ (fun r hr => h₂ r hr)]

end MainFromIC

end ChartKAssembly
end ModularCurve

end

end ChartKFromIC

namespace ModularCurve p2m_export "ModularCurve" "CharPReduction.constSeries CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full NodeLocalized.modularEval NodeLocalized.pointEval NodeLocalized.modularLocalizedAtPoint NodeLocalized.modularEval_mem_modularLocalizedAtPoint ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar coe_geomAut_coeffEmb frobNodePair frobenius_identity_geom_unconditional exists_isFrickeAutFull CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint ssJSet algebraMap_residueField_charLGeomPlaceOfPoint_surjective exists_numberField_presentation isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.coeffEmb_qExpand_comm (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := by
  ext k
  unfold coeffEmb
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full NodeLocalized.modularEval NodeLocalized.pointEval NodeLocalized.modularLocalizedAtPoint NodeLocalized.modularEval_mem_modularLocalizedAtPoint ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar coe_geomAut_coeffEmb frobNodePair frobenius_identity_geom_unconditional exists_isFrickeAutFull CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint ssJSet algebraMap_residueField_charLGeomPlaceOfPoint_surjective exists_numberField_presentation isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver coeffSubring_eq_or_isDiscreteValuationRing isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve.NodeLocalized"
p2m_open "ModularCurve.CharPReduction"

section Eval
variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem modularEval_mem_modularRing (p : MvPolynomial (Fin 2) A) :
    modularEval N A p ∈ modularRing N A := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    exact constSeries_mem_modularRing N A c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · exact jqModC_mem_modularRing N A
    · exact jqNModC_mem_modularRing N A

noncomputable def modularEvalRing : MvPolynomial (Fin 2) A →+* modularRing N A :=
  (modularEval N A).codRestrict _ (modularEval_mem_modularRing N A)

@[scoped simp] theorem coe_modularEvalRing (p : MvPolynomial (Fin 2) A) :
    (modularEvalRing N A p : LaurentSeries L) = modularEval N A p := rfl

noncomputable def modularEvalRed : MvPolynomial (Fin 2) A →+* LaurentSeries k :=
  MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![jqModC k, jqNModC k N]

private theorem red_mk_eq {x : L} (hx : x ∈ A) (y : A) (h : x = (y : L)) : red ⟨x, hx⟩ = red y := by
  subst h; rfl

theorem coeffRed_constSeries (c : A) :
    coeffRed A red ⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ = algebraMap k (LaurentSeries k) (red c) := by
  have hc : ∀ n : ℤ, (constSeries A c).coeff n = if n = 0 then (c : L) else 0 := fun n => by
    show ((algebraMap L (LaurentSeries L)) (c : L)).coeff n = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
    split_ifs <;> rfl
  ext n
  rw [coeffRed_coeff, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  by_cases h : n = 0
  · subst h
    rw [if_pos rfl]
    exact red_mk_eq A red _ c (by rw [show (↑(⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ : integralCoeffs A) : LaurentSeries L) = constSeries A c from rfl, hc, if_pos rfl])
  · rw [if_neg h]
    rw [red_mk_eq A red _ 0 (by rw [show (↑(⟨constSeries A c, constSeries_mem_integralCoeffs A c⟩ : integralCoeffs A) : LaurentSeries L) = constSeries A c from rfl, hc, if_neg h, ZeroMemClass.coe_zero])]
    exact map_zero red

theorem coeffRed_jqModC :
    coeffRed A red ⟨jqModC L, jqModC_mem_integralCoeffs A⟩ = jqModC k := by
  ext n
  rw [coeffRed_coeff]
  rw [red_mk_eq A red _ (((jqModC ℤ).coeff n : ℤ) : A) (by
      show (jqModC L).coeff n = (((((jqModC ℤ).coeff n : ℤ) : A)) : L)
      rw [jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]; simp)]
  rw [map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
  simp

theorem coeffRed_jqNModC :
    coeffRed A red ⟨jqNModC L N, jqNModC_mem_integralCoeffs N A⟩ = jqNModC k N := by
  ext n
  rw [coeffRed_coeff]
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [red_mk_eq A red _ (((jqModC ℤ).coeff m : ℤ) : A) (by
        show (jqNModC L N).coeff (N * m) = (((((jqModC ℤ).coeff m : ℤ) : A)) : L)
        rw [jqNModC, qExpand_coeff_mul, jqModC_eq_map_intCast (K := L), HahnSeries.map_coeff]; simp)]
    rw [map_intCast, jqNModC, qExpand_coeff_mul, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff]
    simp
  · rw [red_mk_eq A red _ 0 (by
        show (jqNModC L N).coeff n = ((0 : A) : L)
        rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h, ZeroMemClass.coe_zero])]
    rw [map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem redRes_modularEvalRing (p : MvPolynomial (Fin 2) A) :
    redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) (modularEvalRing N A p)
      = modularEvalRed N A red p := by
  have key : (redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A)).comp (modularEvalRing N A)
      = modularEvalRed N A red := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, redRes_apply, modularEvalRed, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        ← coeffRed_constSeries A red c]
      exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_C]))
    · rw [RingHom.comp_apply, redRes_apply, modularEvalRed, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · rw [← coeffRed_jqModC A red (L := L)]
        exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_X']; rfl))
      · rw [← coeffRed_jqNModC N A red (L := L)]
        exact congrArg _ (Subtype.ext (by rw [coe_modularEvalRing, modularEval, MvPolynomial.eval₂Hom_X']; rfl))
  exact RingHom.congr_fun key p

end Eval

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve AlgebraicCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full NodeLocalized.modularEval NodeLocalized.pointEval NodeLocalized.modularLocalizedAtPoint NodeLocalized.modularEval_mem_modularLocalizedAtPoint ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar coe_geomAut_coeffEmb frobNodePair frobenius_identity_geom_unconditional exists_isFrickeAutFull CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint ssJSet algebraMap_residueField_charLGeomPlaceOfPoint_surjective exists_numberField_presentation isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve"

section Kron
variable (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q]

theorem jqNModC_one_mul_eq_pow : jqNModC k (1 * q) = jqModC k ^ q := by
  rw [show jqNModC k (1 * q) = jqNModC k q from qExpand_congr (one_mul q) _]
  exact frobenius_identity_geom_unconditional k

end Kron
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict fieldOver coeffSubring_eq_or_isDiscreteValuationRing isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve.NodeLocalized"
section OneVar
variable (q : ℕ) {A : Type*} [CommRing A] {k : Type*} [Field k] (red : A →+* k)

noncomputable def nodePoly : MvPolynomial (Fin 2) A →+* k[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![X, X ^ q]

theorem eval_nodePoly (p : MvPolynomial (Fin 2) A) (b : k) :
    (nodePoly q red p).eval b = MvPolynomial.eval₂Hom red ![b, b ^ q] p := by
  rw [nodePoly, ← Polynomial.coe_evalRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  · ext c; simp
  · funext i; fin_cases i <;> simp

theorem aeval_nodePoly (p : MvPolynomial (Fin 2) A) {S : Type*} [CommRing S] [Algebra k S] (x : S) :
    Polynomial.aeval x (nodePoly q red p)
      = MvPolynomial.eval₂Hom ((algebraMap k S).comp red) ![x, x ^ q] p := by
  rw [nodePoly, ← AlgHom.coe_toRingHom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  · ext c; simp
  · funext i; fin_cases i <;> simp

end OneVar
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"
end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

section Values
variable {k : Type*} [Field k]

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_aux {F : Type*} [Field F] [Algebra k F] (v : Place k F)
    {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

p2m_alias "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.AlgebraicCurve.Place.ord_nonneg_of_mem_aux" "AlgebraicCurve.Place.ord_nonneg_of_mem_aux"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_aux {F : Type*} [Field F] [Algebra k F] (v : Place k F)
    {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_alias "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.AlgebraicCurve.Place.mem_of_ord_nonneg_aux" "AlgebraicCurve.Place.mem_of_ord_nonneg_aux"

private theorem _root_.AlgebraicCurve.Place.HasValue.add {F : Type*} [Field F] [Algebra k F] {v : Place k F}
    {g g' : F} {a a' : k} (h : v.HasValue g a) (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

p2m_alias "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.AlgebraicCurve.Place.HasValue.add" "AlgebraicCurve.Place.HasValue.add"

private theorem _root_.AlgebraicCurve.Place.hasValue_zero_of_ord_pos {F : Type*} [Field F] [Algebra k F] {v : Place k F}
    {g : F} (hg : g ≠ 0) (h : 0 < v.ord g) : v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg_aux hg h.le
  refine ⟨hmem, ?_⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff_adicValuation_lt_one ⟨g, hmem⟩]
  have h1 : v.adicValuation g ≤ 1 := (v.mem_iff_adicValuation_le_one).mp hmem
  refine lt_of_le_of_ne h1 fun heq => ?_
  exact h.ne' ((v.ord_eq_zero_iff_adicValuation_eq_one hg).mpr heq)

p2m_alias "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.AlgebraicCurve.Place.hasValue_zero_of_ord_pos" "AlgebraicCurve.Place.hasValue_zero_of_ord_pos"

noncomputable abbrev jTilde (k : Type*) [Field k] : modularFunctionFieldC k 1 := ⟨jqModC k, jqModC_mem k 1⟩

theorem ratFuncEquivCharLOneC_X (k : Type*) [Field k] : ratFuncEquivCharLOneC k RatFunc.X = jTilde k :=
  Subtype.ext (by
    show ((ratFuncEquivCharLOneC k RatFunc.X : modularFunctionFieldC k 1) : LaurentSeries k) = jqModC k
    rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
    exact RatFunc.algEquivOfTranscendental_X _ _)

theorem ord_charLGeomPlaceOfPoint_jTilde_sub_pos (b : k) :
    0 < (charLGeomPlaceOfPoint k b).ord (jTilde k - algebraMap k _ b) := by
  classical
  let e := ratFuncEquivCharLOneC k
  have he : ∀ c, e.toRingEquiv (algebraMap k (RatFunc k) c) = algebraMap k _ c := fun c => e.commutes c
  have hef : e (RatFunc.X - RatFunc.C b) = jTilde k - algebraMap k _ b := by
    rw [map_sub, ratFuncEquivCharLOneC_X]; exact congrArg _ (e.commutes b)
  have ht := Place.ord_congrRingEquiv e.toRingEquiv he (RationalFunctionField.placeOfPoint k b) (RatFunc.X - RatFunc.C b)
  have hP : Place.congrRingEquiv e.toRingEquiv he (RationalFunctionField.placeOfPoint k b) = charLGeomPlaceOfPoint k b := rfl
  rw [hP] at ht
  change (charLGeomPlaceOfPoint k b).ord (e (RatFunc.X - RatFunc.C b)) = _ at ht
  rw [hef] at ht
  rw [ht]

  have hq0 : (Polynomial.X - Polynomial.C b : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero b
  have hne : (RationalFunctionField.placeOfPoint k b).ord (RatFunc.X - RatFunc.C b) ≠ 0 := by
    rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum, ← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := k) (F := RatFunc k) _ hq0).mpr ?_
    rw [RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal]
    exact Ideal.mem_span_singleton_self _
  have hnn : 0 ≤ (RationalFunctionField.placeOfPoint k b).ord (RatFunc.X - RatFunc.C b) := by
    refine Place.ord_nonneg_of_mem_aux _ ?_
    rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum, ← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
    exact RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum (K := k) _ _
  omega

theorem hasValue_charLGeomPlaceOfPoint_jTilde (b : k) : (charLGeomPlaceOfPoint k b).HasValue (jTilde k) b := by
  have hne : jTilde k - algebraMap k _ b ≠ 0 := fun h => by
    have := ord_charLGeomPlaceOfPoint_jTilde_sub_pos b
    rw [h, Place.ord_zero] at this
    exact lt_irrefl _ this
  have h0 := Place.hasValue_zero_of_ord_pos hne (ord_charLGeomPlaceOfPoint_jTilde_sub_pos b)
  have h1 := (charLGeomPlaceOfPoint k b).hasValue_algebraMap b
  simpa using h0.add h1

theorem hasValue_charLGeomPlaceOfPoint_aeval (b : k) (p : k[X]) :
    (charLGeomPlaceOfPoint k b).HasValue (Polynomial.aeval (jTilde k) p) (p.eval b) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add, Polynomial.eval_add]; exact hp.add hr
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    refine ((charLGeomPlaceOfPoint k b).hasValue_algebraMap c).mul ?_
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact (charLGeomPlaceOfPoint k b).hasValue_one
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul (hasValue_charLGeomPlaceOfPoint_jTilde b)

theorem hasValue_charLGeomPlaceOfPoint_aeval_div (b : k) (p s : k[X]) (hs : s.eval b ≠ 0) :
    (charLGeomPlaceOfPoint k b).HasValue (Polynomial.aeval (jTilde k) p / Polynomial.aeval (jTilde k) s)
      (p.eval b / s.eval b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact (hasValue_charLGeomPlaceOfPoint_aeval b p).mul ((hasValue_charLGeomPlaceOfPoint_aeval b s).inv hs)

end Values
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full NodeLocalized.modularEval NodeLocalized.pointEval NodeLocalized.modularLocalizedAtPoint NodeLocalized.modularEval_mem_modularLocalizedAtPoint ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar coe_geomAut_coeffEmb frobNodePair frobenius_identity_geom_unconditional exists_isFrickeAutFull CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint ssJSet algebraMap_residueField_charLGeomPlaceOfPoint_surjective exists_numberField_presentation isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve"
p2m_open "AlgebraicCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized ModularCurve.CharPReduction"

section LevelQ
variable (q : ℕ) [Fact q.Prime]

local notation "F_" q => modularFunctionFieldBar (1 * q)
local notation "Qb" => AlgebraicClosure ℚ

noncomputable def genJ : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩
noncomputable def genJq : modularFunctionFieldBar (1 * q) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

theorem coe_genJ : ((genJ q : modularFunctionFieldBar (1 * q)) : LaurentSeries Qb) = jqModC Qb := by
  show coeffMap (algebraMap ℚ Qb) (jqModC ℚ) = jqModC Qb
  exact map_jqModC _

theorem coe_genJq : ((genJq q : modularFunctionFieldBar (1 * q)) : LaurentSeries Qb) = jqNModC Qb (1 * q) := by
  show coeffEmb Qb (qExpand ℚ (1 * q) jq) = qExpand Qb (1 * q) (jqModC Qb)
  rw [coeffEmb_qExpand_comm, ← coe_genJ q]; rfl

theorem modularRing_le (A : Subring Qb) :
    modularRing (1 * q) A ≤ (modularFunctionFieldBar (1 * q)).toSubring := by
  rw [modularRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | hx)
  · exact (modularFunctionFieldBar (1 * q)).algebraMap_mem (c : Qb)
  · rcases hx with rfl | hx'
    · rw [← coe_genJ q]; exact (genJ q).2
    · rw [Set.mem_singleton_iff] at hx'
      rw [hx', ← coe_genJq q]; exact (genJq q).2

noncomputable def modularEvalF (A : Subring Qb) : MvPolynomial (Fin 2) A →+* modularFunctionFieldBar (1 * q) :=
  (modularEval (1 * q) A).codRestrict (modularFunctionFieldBar (1 * q)).toSubring
    (fun p => modularRing_le q A (modularEval_mem_modularRing (1 * q) A p))

@[scoped simp] theorem coe_modularEvalF (A : Subring Qb) (p : MvPolynomial (Fin 2) A) :
    ((modularEvalF q A p : modularFunctionFieldBar (1 * q)) : LaurentSeries Qb) = modularEval (1 * q) A p := rfl

theorem modularEvalF_X0 (A : Subring Qb) : modularEvalF q A (MvPolynomial.X 0) = genJ q :=
  Subtype.ext (by rw [coe_modularEvalF, modularEval, MvPolynomial.eval₂Hom_X', coe_genJ]; rfl)
theorem modularEvalF_X1 (A : Subring Qb) : modularEvalF q A (MvPolynomial.X 1) = genJq q :=
  Subtype.ext (by rw [coe_modularEvalF, modularEval, MvPolynomial.eval₂Hom_X', coe_genJq]; rfl)
theorem modularEvalF_C (A : Subring Qb) (c : A) :
    modularEvalF q A (MvPolynomial.C c) = algebraMap Qb (modularFunctionFieldBar (1 * q)) (c : Qb) :=
  Subtype.ext (by rw [coe_modularEvalF, modularEval, MvPolynomial.eval₂Hom_C]; rfl)

theorem frickeInvolutionBar_genJ :
    frickeInvolutionBar (1 * q) (genJ q) = genJq q ∧ frickeInvolutionBar (1 * q) (genJq q) = genJ q := by
  haveI : Fact (Nat.Prime (1 * q)) := ⟨by rw [one_mul]; exact Fact.out⟩
  have hσ : IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
    isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull (1 * q))
  have h1q := hσ 1 q rfl inferInstance inferInstance
  have hq1 := hσ q 1 (by ring) inferInstance inferInstance
  have e1 : ∀ (h : qExpand ℚ 1 jq ∈ modularFunctionFieldFull (1 * q)) (h' : jq ∈ modularFunctionFieldFull (1 * q)),
      (⟨qExpand ℚ 1 jq, h⟩ : modularFunctionFieldFull (1 * q)) = ⟨jq, h'⟩ :=
    fun h h' => Subtype.ext (qExpand_one_apply _)
  have eq : ∀ (h : qExpand ℚ q jq ∈ modularFunctionFieldFull (1 * q)) (h' : qExpand ℚ (1 * q) jq ∈ modularFunctionFieldFull (1 * q)),
      (⟨qExpand ℚ q jq, h⟩ : modularFunctionFieldFull (1 * q)) = ⟨qExpand ℚ (1 * q) jq, h'⟩ :=
    fun h h' => Subtype.ext (qExpand_congr (one_mul q).symm _)
  have hjq : jq ∈ modularFunctionFieldFull (1 * q) := modularFunctionField_le_full (1 * q) (jq_mem (1 * q))
  have hjQ : qExpand ℚ (1 * q) jq ∈ modularFunctionFieldFull (1 * q) := jqd_mem_full (1 * q) (dvd_refl (1 * q))
  constructor
  · apply Subtype.ext
    refine (coe_geomAut_coeffEmb Qb (modularFunctionFieldFull (1 * q)) (frickeInvolutionFull (1 * q)) ⟨jq, hjq⟩).trans ?_
    show coeffEmb Qb ((frickeInvolutionFull (1 * q) ⟨jq, hjq⟩ : modularFunctionFieldFull (1 * q)) : LaurentSeries ℚ)
      = coeffEmb Qb (qExpand ℚ (1 * q) jq)
    rw [← e1 (jqd_mem_full (1 * q) (Dvd.intro q rfl)) hjq, h1q, qExpand_congr (one_mul q) jq]
  · apply Subtype.ext
    refine (coe_geomAut_coeffEmb Qb (modularFunctionFieldFull (1 * q)) (frickeInvolutionFull (1 * q)) ⟨_, hjQ⟩).trans ?_
    show coeffEmb Qb ((frickeInvolutionFull (1 * q) ⟨qExpand ℚ (1 * q) jq, hjQ⟩ : modularFunctionFieldFull (1 * q)) : LaurentSeries ℚ)
      = coeffEmb Qb jq
    rw [← eq (jqd_mem_full (1 * q) (Dvd.intro _ (by ring : q * 1 = 1 * q))) hjQ, hq1,
      e1 _ hjq]

theorem frickeInvolutionBar_modularEvalF (A : Subring Qb) (p : MvPolynomial (Fin 2) A) :
    frickeInvolutionBar (1 * q) (modularEvalF q A p) = modularEvalF q A (MvPolynomial.rename (Equiv.swap 0 1) p) := by
  have key : (frickeInvolutionBar (1 * q)).toAlgHom.toRingHom.comp (modularEvalF q A)
      = (modularEvalF q A).comp (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgEquiv.coe_algHom, MvPolynomial.rename_C]
      rw [modularEvalF_C, AlgEquiv.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgEquiv.coe_algHom, MvPolynomial.rename_X]
      fin_cases i
      · show frickeInvolutionBar (1 * q) (modularEvalF q A (MvPolynomial.X 0)) = modularEvalF q A (MvPolynomial.X (Equiv.swap 0 1 0))
        rw [Equiv.swap_apply_left, modularEvalF_X0, modularEvalF_X1]; exact (frickeInvolutionBar_genJ q).1
      · show frickeInvolutionBar (1 * q) (modularEvalF q A (MvPolynomial.X 1)) = modularEvalF q A (MvPolynomial.X (Equiv.swap 0 1 1))
        rw [Equiv.swap_apply_right, modularEvalF_X0, modularEvalF_X1]; exact (frickeInvolutionBar_genJ q).2
  exact RingHom.congr_fun key p

end LevelQ
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

section DOM
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] (red : A →+* k)

theorem modularEvalRed_eq_aeval (p : MvPolynomial (Fin 2) A.toSubring) :
    modularEvalRed (1 * q) A.toSubring red p = Polynomial.aeval (jqModC k) (nodePoly q red p) := by
  rw [aeval_nodePoly, modularEvalRed, ← jqNModC_one_mul_eq_pow q k]

theorem modularEvalRed_ne_zero {p : MvPolynomial (Fin 2) A.toSubring} {b : k} (hb : (nodePoly q red p).eval b ≠ 0) :
    modularEvalRed (1 * q) A.toSubring red p ≠ 0 := by
  rw [modularEvalRed_eq_aeval]
  intro h
  have hp : nodePoly q red p ≠ 0 := fun h0 => hb (by rw [h0, Polynomial.eval_zero])
  exact transcendental_jqModC k ⟨nodePoly q red p, hp, h⟩

theorem modularRedLocHom_mem_one {L : Type*} [CommRing L] (B : Subring L) (red' : B →+* k)
    (x : modularLocalized (1 * q) B red') : modularRedLocHom (1 * q) B red' x ∈ modularFunctionFieldC k 1 := by
  have h := CharPReduction.modularRedLocHom_mem B red' (1 * q) x
  have e : modularFunctionFieldC k (1 * q) = modularFunctionFieldC k 1 := by
    rw [← modularFunctionFieldC_self_collapse_unconditional k (ℓ := q)]
    show IntermediateField.adjoin k {jqModC k, jqNModC k (1 * q)} = IntermediateField.adjoin k {jqModC k, jqNModC k q}
    rw [show jqNModC k (1 * q) = jqNModC k q from qExpand_congr (one_mul q) _]
  rw [e] at h; exact h

theorem exists_hasValue_of_presentation (g : LaurentSeries (AlgebraicClosure ℚ)) (r s : MvPolynomial (Fin 2) A.toSubring)
    (hgs : g * modularEval (1 * q) A.toSubring s = modularEval (1 * q) A.toSubring r) (b : k)
    (hb : (nodePoly q red s).eval b ≠ 0) :
    ∃ (h₁ : g ∈ modularLocalized (1 * q) A.toSubring red)
      (h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1),
      (charLGeomPlaceOfPoint k b).HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1)
        ((nodePoly q red r).eval b / (nodePoly q red s).eval b) := by
  have hsK : modularEvalRed (1 * q) A.toSubring red s ≠ 0 := modularEvalRed_ne_zero red hb
  have hs_notin : modularEvalRing (1 * q) A.toSubring s ∉
      redKer A.toSubring red (modularRing (1 * q) A.toSubring) (modularRing_le_integralCoeffs (1 * q) A.toSubring) := by
    rw [notMem_redKer_iff, redRes_modularEvalRing]; exact hsK
  have h₁ : g ∈ modularLocalized (1 * q) A.toSubring red :=
    ⟨modularEvalRing (1 * q) A.toSubring r, modularEvalRing (1 * q) A.toSubring s, hs_notin, by simpa using hgs⟩
  have hπ : modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩
      = modularEvalRed (1 * q) A.toSubring red r / modularEvalRed (1 * q) A.toSubring red s := by
    rw [eq_div_iff hsK]
    have := redLoc_spec (A := A.toSubring) (red := red) (R := modularRing (1 * q) A.toSubring)
      (hR := modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨g, h₁⟩
      (r := modularEvalRing (1 * q) A.toSubring r) (s := modularEvalRing (1 * q) A.toSubring s) (by simpa using hgs)
    rw [redRes_modularEvalRing, redRes_modularEvalRing] at this
    exact this
  have h₁F := modularRedLocHom_mem_one A.toSubring red ⟨g, h₁⟩
  refine ⟨h₁, h₁F, ?_⟩
  have hval := hasValue_charLGeomPlaceOfPoint_aeval_div b (nodePoly q red r) (nodePoly q red s) hb
  have heq : (⟨_, h₁F⟩ : modularFunctionFieldC k 1)
      = Polynomial.aeval (jTilde k) (nodePoly q red r) / Polynomial.aeval (jTilde k) (nodePoly q red s) := by
    apply Subtype.ext
    show modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ = _
    rw [hπ, modularEvalRed_eq_aeval, modularEvalRed_eq_aeval]
    have hcoe : ∀ p : k[X], ((Polynomial.aeval (jTilde k) p : modularFunctionFieldC k 1) : LaurentSeries k)
        = Polynomial.aeval (jqModC k) p := fun p =>
      (Polynomial.aeval_algHom_apply (modularFunctionFieldC k 1).val (jTilde k) p).symm
    rw [show ((Polynomial.aeval (jTilde k) (nodePoly q red r) / Polynomial.aeval (jTilde k) (nodePoly q red s)
          : modularFunctionFieldC k 1) : LaurentSeries k)
        = ((Polynomial.aeval (jTilde k) (nodePoly q red r) : modularFunctionFieldC k 1) : LaurentSeries k)
          / ((Polynomial.aeval (jTilde k) (nodePoly q red s) : modularFunctionFieldC k 1) : LaurentSeries k)
        from map_div₀ (modularFunctionFieldC k 1).val _ _, hcoe, hcoe]
  rw [heq]; exact hval

end DOM
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply qExpand_congr jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full NodeLocalized.modularEval NodeLocalized.pointEval NodeLocalized.modularLocalizedAtPoint NodeLocalized.modularEval_mem_modularLocalizedAtPoint ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar coe_geomAut_coeffEmb frobNodePair frobenius_identity_geom_unconditional exists_isFrickeAutFull CharPReduction.modularRedLocHom_mem modularFunctionFieldC_self_collapse_unconditional exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint ssJSet algebraMap_residueField_charLGeomPlaceOfPoint_surjective exists_numberField_presentation isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve"
p2m_open "AlgebraicCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized ModularCurve.CharPReduction Polynomial"

section RedFacts

theorem red_eq_zero_of_mem_maximalIdeal (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
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

theorem isLocalHom_red (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) : IsLocalHom red := by
  constructor
  intro τ hτ
  by_contra hnu
  have h0 := red_eq_zero_of_mem_maximalIdeal q red τ ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  rw [h0] at hτ
  exact not_isUnit_zero hτ

theorem mem_fieldRange_lift_red_of_monic (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) [IsLocalHom red] (y : k)
    (P : Polynomial (IsLocalRing.ResidueField A)) (hP : P.Monic)
    (hy : P.eval₂ (IsLocalRing.ResidueField.lift red) y = 0) :
    y ∈ (IsLocalRing.ResidueField.lift red).fieldRange := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  letI : Algebra (IsLocalRing.ResidueField A) k := (IsLocalRing.ResidueField.lift red).toAlgebra
  have hint : IsIntegral (IsLocalRing.ResidueField A) y := ⟨P, hP, hy⟩
  have h1 : (minpoly (IsLocalRing.ResidueField A) y).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hint)
  obtain ⟨t, ht⟩ := minpoly.mem_range_of_degree_eq_one _ y h1
  exact ⟨t, ht⟩

theorem mem_fieldRange_lift_red_coordinate (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) [IsLocalHom red] (a : k) (ha2 : a ^ (q ^ 2) = a) :
    a ∈ (IsLocalRing.ResidueField.lift red).fieldRange := by
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Fact.out : q.Prime).pos
  have hdeg : (Polynomial.X : Polynomial (IsLocalRing.ResidueField A)).degree < ((q ^ 2 - 1 + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_X]
    have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    have h22 : 2 ≤ q ^ 2 := by nlinarith
    exact_mod_cast (show 1 < q ^ 2 - 1 + 1 by omega)
  refine mem_fieldRange_lift_red_of_monic q red a (Polynomial.X ^ (q ^ 2 - 1 + 1) - Polynomial.X)
    (Polynomial.monic_X_pow_sub hdeg) ?_
  rw [Nat.sub_add_cancel hq2, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, ha2, sub_self]

theorem pointEval_mem_fieldRange_lift_red (q : ℕ) [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) [IsLocalHom red] (a : k) (ha2 : a ^ (q ^ 2) = a)
    (r : MvPolynomial (Fin 2) A.toSubring) :
    pointEval A.toSubring red a (a ^ q) r ∈ (IsLocalRing.ResidueField.lift red).fieldRange := by
  set S := (IsLocalRing.ResidueField.lift red).fieldRange
  have ha : a ∈ S := mem_fieldRange_lift_red_coordinate q red a ha2
  have hred : ∀ c : A.toSubring, red c ∈ S := fun c =>
    ⟨IsLocalRing.residue A c, IsLocalRing.ResidueField.lift_residue_apply red c⟩
  induction r using MvPolynomial.induction_on with
  | C c => rw [pointEval, MvPolynomial.eval₂Hom_C]; exact hred c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [pointEval, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · exact ha
    · exact pow_mem ha q

end RedFacts
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

section GLUE
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k]

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

omit [DecidableEq k] in
theorem modularEval_ne_zero_of_eval_nodePoly_ne_zero (red : A →+* k) {s : MvPolynomial (Fin 2) A.toSubring} {a : k}
    (hs : (nodePoly q red s).eval a ≠ 0) : modularEval (1 * q) A.toSubring s ≠ 0 := by
  intro h0
  apply modularEvalRed_ne_zero red hs
  rw [← redRes_modularEvalRing]
  have : modularEvalRing (1 * q) A.toSubring s = 0 := Subtype.ext h0
  rw [this, map_zero]

omit [Fact q.Prime] [CharP k q] [DecidableEq k] in
theorem eval_nodePoly_eq_pointEval (red : A →+* k) (a : k) (p : MvPolynomial (Fin 2) A.toSubring) :
    (nodePoly q red p).eval a = pointEval A.toSubring red a (a ^ q) p := by
  rw [eval_nodePoly]; rfl

omit [DecidableEq k] in
theorem nodeRing_le_modularLocalized (red : A →+* k) (a : k) :
    modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) ≤ modularLocalized (1 * q) A.toSubring red := by
  rintro g ⟨r, s, hs, hgs⟩
  have hb : (nodePoly q red s).eval a ≠ 0 := by rw [eval_nodePoly_eq_pointEval]; exact hs
  exact (exists_hasValue_of_presentation red g r s hgs a hb).1

omit [DecidableEq k] in
theorem nodeRing_le_field (red : A →+* k) (a : k) :
    modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) ≤ (modularFunctionFieldBar (1 * q)).toSubring := by
  rintro g ⟨r, s, hs, hgs⟩
  have hb : (nodePoly q red s).eval a ≠ 0 := by rw [eval_nodePoly_eq_pointEval]; exact hs
  have hs0 := modularEval_ne_zero_of_eval_nodePoly_ne_zero red hb
  have hg : g = modularEval (1 * q) A.toSubring r * (modularEval (1 * q) A.toSubring s)⁻¹ := by
    rw [← hgs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hg]
  exact mul_mem (modularRing_le q A.toSubring (modularEval_mem_modularRing _ _ r))
    ((modularFunctionFieldBar (1 * q)).inv_mem (modularRing_le q A.toSubring (modularEval_mem_modularRing _ _ s)))

omit [DecidableEq k] in
theorem hasValue_nodeRing_presentation (red : A →+* k) (a : k)
    {g : LQ} {r s : MvPolynomial (Fin 2) A.toSubring} (hs : pointEval A.toSubring red a (a ^ q) s ≠ 0)
    (hgs : g * modularEval (1 * q) A.toSubring s = modularEval (1 * q) A.toSubring r)
    (h₁ : g ∈ modularLocalized (1 * q) A.toSubring red)
    (h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨g, h₁⟩ ∈ modularFunctionFieldC k 1) :
    (charLGeomPlaceOfPoint k a).HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1)
      (pointEval A.toSubring red a (a ^ q) r / pointEval A.toSubring red a (a ^ q) s) := by
  have hb : (nodePoly q red s).eval a ≠ 0 := by rw [eval_nodePoly_eq_pointEval]; exact hs
  obtain ⟨h₁', h₁F', hv⟩ := exists_hasValue_of_presentation red g r s hgs a hb
  rw [eval_nodePoly_eq_pointEval, eval_nodePoly_eq_pointEval] at hv
  exact hv

noncomputable def redF (red : A →+* k) : modularLocalized (1 * q) A.toSubring red →+* modularFunctionFieldC k 1 where
  toFun x := ⟨modularRedLocHom (1 * q) A.toSubring red x, modularRedLocHom_mem_one A.toSubring red x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

omit [Fact q.Prime] [CharP k q] [DecidableEq k] in
theorem n3_mem_coeffSubring_iff (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {x : AlgebraicClosure ℚ} :
    x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

noncomputable abbrev n3incl (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(coeffSubring A K) →+* ↥A.toSubring :=
  Subring.inclusion inf_le_left

theorem n3_modularEval_map (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) A.toSubring (MvPolynomial.map (n3incl A K) r) = modularEval (1 * q) (coeffSubring A K) r := by
  unfold modularEval
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

omit [Fact q.Prime] [CharP k q] [DecidableEq k] in
theorem n3_pointEval_map (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (red : A →+* k) (a b : k)
    (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    pointEval A.toSubring red a b (MvPolynomial.map (n3incl A K) r) = pointEval (coeffSubring A K) (redRestrict red K) a b r := by
  unfold pointEval
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

omit [Fact q.Prime] [CharP k q] [DecidableEq k] in

theorem n3_exists_map_eq (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (r : MvPolynomial (Fin 2) ↥A.toSubring)
    (hr : ∀ m ∈ r.support, ((r.coeff m : ↥A.toSubring) : AlgebraicClosure ℚ) ∈ K) :
    ∃ r₀ : MvPolynomial (Fin 2) ↥(coeffSubring A K), MvPolynomial.map (n3incl A K) r₀ = r := by
  classical
  refine ⟨∑ m ∈ r.support.attach, MvPolynomial.monomial m.1
    ⟨((r.coeff m.1 : ↥A.toSubring) : AlgebraicClosure ℚ), (r.coeff m.1).2, hr m.1 m.2⟩, ?_⟩
  rw [map_sum]
  conv_rhs => rw [r.as_sum, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial]
  rfl

theorem n3_modularEval_mem_fieldOver {K' K : IntermediateField ℚ (AlgebraicClosure ℚ)} (hK : K' ≤ K)
    (r : MvPolynomial (Fin 2) ↥(coeffSubring A K')) :
    modularEval (1 * q) (coeffSubring A K') r ∈ fieldOver (1 * q) K := by
  induction r using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    refine Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), ?_⟩, rfl⟩)
    exact hK ((n3_mem_coeffSubring_iff K').mp c.2).2
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, MvPolynomial.eval₂Hom_X']
    refine Subfield.subset_closure (Or.inr ?_)
    fin_cases i <;> simp

omit [DecidableEq k] in

theorem n3_descended_le (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (red : A →+* k) (a : k) :
    modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
      ≤ modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) := by
  rintro g ⟨r, s, hs, hgs⟩
  refine ⟨MvPolynomial.map (n3incl A K) r, MvPolynomial.map (n3incl A K) s, ?_, ?_⟩
  · rwa [n3_pointEval_map]
  · rwa [n3_modularEval_map, n3_modularEval_map]

omit [DecidableEq k] in

theorem n3_descended_le_fieldOver (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (red : A →+* k) (a : k) :
    modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ≤ (fieldOver (1 * q) K).toSubring := by
  rintro g ⟨r, s, hs, hgs⟩
  have hs' : (nodePoly q red (MvPolynomial.map (n3incl A K) s)).eval a ≠ 0 := by
    rw [eval_nodePoly_eq_pointEval, n3_pointEval_map]; exact hs
  have hs0 : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := by
    rw [← n3_modularEval_map]; exact modularEval_ne_zero_of_eval_nodePoly_ne_zero red hs'
  have hg : g = modularEval (1 * q) (coeffSubring A K) r * (modularEval (1 * q) (coeffSubring A K) s)⁻¹ := by
    rw [← hgs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hg]
  show _ ∈ fieldOver (1 * q) K
  exact mul_mem (n3_modularEval_mem_fieldOver le_rfl r) ((fieldOver (1 * q) K).inv_mem (n3_modularEval_mem_fieldOver le_rfl s))

theorem chart_a_small (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hq : q < 5)
    (B : Subring (LaurentSeries (AlgebraicClosure ℚ)))
    (hBF : B ≤ (modularFunctionFieldBar (1 * q)).toSubring)
    (hNB : NodeLocalized.modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) ≤ B)
    (hint : ∀ x ∈ B, IsIntegral ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q)) x)
    (P₁ P₂ : Ideal ↥B) [P₁.IsPrime] [P₂.IsPrime]
    (h₁ : ∀ r : MvPolynomial (Fin 2) ↥A.toSubring, NodeLocalized.pointEval A.toSubring red a (a ^ q) r = 0 →
      (⟨NodeLocalized.modularEval (1 * q) A.toSubring r,
        hNB (NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r)⟩ : ↥B) ∈ P₁)
    (h₂ : ∀ r : MvPolynomial (Fin 2) ↥A.toSubring, NodeLocalized.pointEval A.toSubring red a (a ^ q) r = 0 →
      (⟨NodeLocalized.modularEval (1 * q) A.toSubring r,
        hNB (NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r)⟩ : ↥B) ∈ P₂) :
    P₁ = P₂ := by
  classical
  haveI : IsLocalHom red := isLocalHom_red q red

  obtain ⟨t, ht⟩ := mem_fieldRange_lift_red_coordinate q red a ha2
  obtain ⟨c0, hc0⟩ := IsLocalRing.residue_surjective t
  have hredc0 : red c0 = a := by rw [← ht, ← hc0, IsLocalRing.ResidueField.lift_residue_apply]
  set Na := NodeLocalized.modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) with hNa

  suffices key : ∀ (Q₁ Q₂ : Ideal ↥B) [Q₁.IsPrime] [Q₂.IsPrime],
      (∀ r : MvPolynomial (Fin 2) ↥A.toSubring, NodeLocalized.pointEval A.toSubring red a (a ^ q) r = 0 →
        (⟨NodeLocalized.modularEval (1 * q) A.toSubring r,
          hNB (NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r)⟩ : ↥B) ∈ Q₁) →
      (∀ r : MvPolynomial (Fin 2) ↥A.toSubring, NodeLocalized.pointEval A.toSubring red a (a ^ q) r = 0 →
        (⟨NodeLocalized.modularEval (1 * q) A.toSubring r,
          hNB (NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r)⟩ : ↥B) ∈ Q₂) →
      Q₁ ≤ Q₂ by
    exact le_antisymm (key P₁ P₂ h₁ h₂) (key P₂ P₁ h₂ h₁)
  intro Q₁ Q₂ _ _ hQ₁ hQ₂ b hb1

  obtain ⟨Kb, hKb, Pb, Qb0, hQb0, hbpres⟩ := ModularCurve.exists_numberField_presentation A ⟨(b : LQ), hBF b.2⟩
  haveI := hKb

  obtain ⟨p, hpmonic, hpb⟩ := hint (b : LQ) b.2
  have hc : ∀ n : ℕ, ∃ r s : MvPolynomial (Fin 2) ↥A.toSubring,
      pointEval A.toSubring red a (a ^ q) s ≠ 0 ∧ ((p.coeff n : ↥Na) : LQ) * modularEval (1 * q) A.toSubring s
        = modularEval (1 * q) A.toSubring r := fun n => (p.coeff n).2
  choose pr ps hps hpres using hc
  let S : Finset (AlgebraicClosure ℚ) := {((c0 : ↥A) : AlgebraicClosure ℚ)} ∪
    (Finset.range (p.natDegree + 1)).biUnion (fun n =>
      ((pr n).support.image (fun m => (((pr n).coeff m : ↥A.toSubring) : AlgebraicClosure ℚ))) ∪
      ((ps n).support.image (fun m => (((ps n).coeff m : ↥A.toSubring) : AlgebraicClosure ℚ))))
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := Kb ⊔ IntermediateField.adjoin ℚ (S : Set (AlgebraicClosure ℚ))
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ (S : Set (AlgebraicClosure ℚ))) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : FiniteDimensional ℚ ↥K := IntermediateField.finiteDimensional_sup Kb _
  have hSK : ∀ x ∈ S, x ∈ K := fun x hx =>
    (le_sup_right : IntermediateField.adjoin ℚ (S : Set (AlgebraicClosure ℚ)) ≤ K) (IntermediateField.subset_adjoin ℚ _ hx)
  have hKbK : Kb ≤ K := le_sup_left

  set R₀ := modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) with hR₀
  have hR₀Na : R₀ ≤ Na := n3_descended_le K red a
  have hR₀B : R₀ ≤ B := hR₀Na.trans hNB

  have hcoefK : ∀ n ∈ Finset.range (p.natDegree + 1),
      (∀ m ∈ (pr n).support, (((pr n).coeff m : ↥A.toSubring) : AlgebraicClosure ℚ) ∈ K) ∧
      (∀ m ∈ (ps n).support, (((ps n).coeff m : ↥A.toSubring) : AlgebraicClosure ℚ) ∈ K) := by
    intro n hn
    refine ⟨fun m hm => hSK _ ?_, fun m hm => hSK _ ?_⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_union_left _ ?_⟩)
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_union_right _ ?_⟩)
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
  have hcoefR₀ : ∀ n, ((p.coeff n : ↥Na) : LQ) ∈ R₀ := by
    intro n
    by_cases hn : n ∈ Finset.range (p.natDegree + 1)
    · obtain ⟨r₀, hr₀⟩ := n3_exists_map_eq K (pr n) (hcoefK n hn).1
      obtain ⟨s₀, hs₀⟩ := n3_exists_map_eq K (ps n) (hcoefK n hn).2
      refine ⟨r₀, s₀, ?_, ?_⟩
      · rw [← n3_pointEval_map, hs₀]; exact hps n
      · rw [← n3_modularEval_map, ← n3_modularEval_map, hr₀, hs₀]; exact hpres n
    · have : p.coeff n = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simpa [Finset.mem_range] using hn
      rw [this]; exact zero_mem _

  have hbR₀ : IsIntegral ↥R₀ (b : LQ) := by
    have hlifts : p ∈ Polynomial.lifts (Subring.inclusion hR₀Na) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hcoefR₀ n⟩, Subtype.ext rfl⟩
    obtain ⟨p₀, hp₀map, -, hp₀monic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hpmonic
    refine ⟨p₀, hp₀monic, ?_⟩
    have : (algebraMap ↥Na LQ).comp (Subring.inclusion hR₀Na) = algebraMap ↥R₀ LQ := RingHom.ext fun _ => rfl
    rw [← this, ← Polynomial.eval₂_map, hp₀map]
    exact hpb

  have hbF₀ : (b : LQ) ∈ fieldOver (1 * q) K := by
    have hQ : modularEval (1 * q) (coeffSubring A Kb) Qb0 ∈ fieldOver (1 * q) K := n3_modularEval_mem_fieldOver hKbK Qb0
    have hP : modularEval (1 * q) (coeffSubring A Kb) Pb ∈ fieldOver (1 * q) K := n3_modularEval_mem_fieldOver hKbK Pb
    have hb : (b : LQ) = modularEval (1 * q) (coeffSubring A Kb) Pb * (modularEval (1 * q) (coeffSubring A Kb) Qb0)⁻¹ := by
      rw [← hbpres]; exact (mul_inv_cancel_right₀ hQb0 _).symm
    rw [hb]
    exact mul_mem hP (inv_mem hQ)

  let B₀ : Subring LQ := Subring.closure ((R₀ : Set LQ) ∪ {(b : LQ)})
  have hR₀B₀ : R₀ ≤ B₀ := fun x hx => Subring.subset_closure (Or.inl hx)
  have hbB₀ : (b : LQ) ∈ B₀ := Subring.subset_closure (Or.inr rfl)
  have hB₀B : B₀ ≤ B :=
    Subring.closure_le.mpr (Set.union_subset hR₀B (Set.singleton_subset_iff.mpr b.2))
  have hB₀F : B₀ ≤ (fieldOver (1 * q) K).toSubring :=
    Subring.closure_le.mpr (Set.union_subset (n3_descended_le_fieldOver K red a) (Set.singleton_subset_iff.mpr hbF₀))
  have hB₀int : ∀ x ∈ B₀, IsIntegral ↥R₀ x := by
    have hle : B₀ ≤ (integralClosure ↥R₀ LQ).toSubring := Subring.closure_le.mpr (Set.union_subset
      (fun x hx => (integralClosure ↥R₀ LQ).algebraMap_mem ⟨x, hx⟩)
      (Set.singleton_subset_iff.mpr (show (b : LQ) ∈ integralClosure ↥R₀ LQ from hbR₀)))
    exact fun x hx => (show x ∈ integralClosure ↥R₀ LQ from hle hx)

  let ι : ↥B₀ →+* ↥B := Subring.inclusion hB₀B
  have hgen : ∀ (Q : Ideal ↥B),
      (∀ r : MvPolynomial (Fin 2) ↥A.toSubring, NodeLocalized.pointEval A.toSubring red a (a ^ q) r = 0 →
        (⟨NodeLocalized.modularEval (1 * q) A.toSubring r,
          hNB (NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r)⟩ : ↥B) ∈ Q) →
      ∀ r : MvPolynomial (Fin 2) ↥(coeffSubring A K), pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) r = 0 →
        (⟨modularEval (1 * q) (coeffSubring A K) r,
          hR₀B₀ (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) r)⟩ : ↥B₀)
          ∈ Q.comap ι := by
    intro Q hQ r hr
    rw [Ideal.mem_comap]
    have h := hQ (MvPolynomial.map (n3incl A K) r) (by rw [n3_pointEval_map]; exact hr)
    convert h using 1
    exact Subtype.ext (n3_modularEval_map K r).symm
  have hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a := by
    refine ⟨⟨((c0 : ↥A) : AlgebraicClosure ℚ), (n3_mem_coeffSubring_iff K).mpr ⟨c0.2, hSK _ ?_⟩⟩, ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    · rw [← hredc0]; rfl

  have hkey := ModularCurve.ChartKAssembly.chartK_of_isIntegrallyClosed red a K hx
    (ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five red a ha ha2 hq K hx) B₀ hB₀F hR₀B₀ hB₀int (Q₁.comap ι) (Q₂.comap ι) (hgen Q₁ hQ₁) (hgen Q₂ hQ₂)
  have hb₀ : (⟨(b : LQ), hbB₀⟩ : ↥B₀) ∈ Q₁.comap ι := by
    rw [Ideal.mem_comap]
    convert hb1 using 1
    all_goals first | rfl | exact Subtype.ext rfl | (apply Subtype.ext; simp [ι, Subring.coe_inclusion])
  rw [hkey, Ideal.mem_comap] at hb₀
  convert hb₀ using 1
  all_goals first | rfl | exact Subtype.ext rfl | (apply Subtype.ext; simp [ι, Subring.coe_inclusion])

theorem _root_.P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.solution
    (red : A →+* k) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hq : q < 5)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (hint : IsIntegral ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q)) (f : LaurentSeries (AlgebraicClosure ℚ)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1) :
    ∃ c : k,
      (frobNodePair q a).1.HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (⟨_, h₂F⟩ : modularFunctionFieldC k 1) c := by
  classical
  haveI : IsLocalHom red := isLocalHom_red q red

  set Na := NodeLocalized.modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) with hNa
  let B : Subring LQ := Subring.closure ((Na : Set LQ) ∪ {(f : LQ)})
  have hNaB : Na ≤ B := fun x hx => Subring.subset_closure (Or.inl hx)
  have hfB : (f : LQ) ∈ B := Subring.subset_closure (Or.inr rfl)
  have hBF : B ≤ (modularFunctionFieldBar (1 * q)).toSubring :=
    Subring.closure_le.mpr (Set.union_subset (nodeRing_le_field red a) (Set.singleton_subset_iff.mpr f.2))
  have hBint : ∀ x ∈ B, IsIntegral ↥Na x := by
    have hle : B ≤ (integralClosure ↥Na LQ).toSubring := Subring.closure_le.mpr (Set.union_subset
      (fun x hx => (integralClosure ↥Na LQ).algebraMap_mem ⟨x, hx⟩)
      (Set.singleton_subset_iff.mpr (show (f : LQ) ∈ integralClosure ↥Na LQ from hint)))
    exact fun x hx => (show x ∈ integralClosure ↥Na LQ from hle hx)
  have hBML : B ≤ modularLocalized (1 * q) A.toSubring red :=
    Subring.closure_le.mpr (Set.union_subset (nodeRing_le_modularLocalized red a) (Set.singleton_subset_iff.mpr h₁))

  have hBw : ∀ x (hx : x ∈ B), ((frickeInvolutionBar (1 * q) ⟨x, hBF hx⟩ : modularFunctionFieldBar (1 * q)) : LQ)
      ∈ modularLocalized (1 * q) A.toSubring red := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · obtain ⟨_, _, h2, _, _⟩ := ModularCurve.exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint red a ha2
          ⟨y, nodeRing_le_field red a hy⟩ hy
        exact h2
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        have : (⟨(f : LQ), hBF (Subring.subset_closure (Or.inr rfl))⟩ : modularFunctionFieldBar (1 * q)) = f := Subtype.ext rfl
        rw [this]; exact h₂
    | zero =>
      have : (⟨(0 : LQ), hBF (zero_mem B)⟩ : modularFunctionFieldBar (1 * q)) = 0 := Subtype.ext rfl
      rw [this, map_zero]; exact zero_mem _
    | one =>
      have : (⟨(1 : LQ), hBF (one_mem B)⟩ : modularFunctionFieldBar (1 * q)) = 1 := Subtype.ext rfl
      rw [this, map_one]; exact one_mem _
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hBF (add_mem hx hy)⟩ : modularFunctionFieldBar (1 * q)) = ⟨x, hBF hx⟩ + ⟨y, hBF hy⟩ := Subtype.ext rfl
      rw [this, map_add]; exact add_mem ihx ihy
    | neg x hx ihx =>
      have : (⟨-x, hBF (neg_mem hx)⟩ : modularFunctionFieldBar (1 * q)) = -⟨x, hBF hx⟩ := Subtype.ext rfl
      rw [this, map_neg]; exact neg_mem ihx
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, hBF (mul_mem hx hy)⟩ : modularFunctionFieldBar (1 * q)) = ⟨x, hBF hx⟩ * ⟨y, hBF hy⟩ := Subtype.ext rfl
      rw [this, map_mul]; exact mul_mem ihx ihy

  let Φ₁ : B →+* modularFunctionFieldC k 1 := (redF red).comp (Subring.inclusion hBML)
  let ιw : B →+* modularLocalized (1 * q) A.toSubring red :=
    { toFun := fun x => ⟨_, hBw x.1 x.2⟩
      map_one' := Subtype.ext (by
        show ((frickeInvolutionBar (1 * q) ⟨(1 : LQ), _⟩ : modularFunctionFieldBar (1 * q)) : LQ) = 1
        rw [show (⟨(1 : LQ), hBF (one_mem B)⟩ : modularFunctionFieldBar (1 * q)) = 1 from Subtype.ext rfl, map_one]; rfl)
      map_mul' := fun x y => Subtype.ext (by
        show ((frickeInvolutionBar (1 * q) ⟨(x : LQ) * y, _⟩ : modularFunctionFieldBar (1 * q)) : LQ) = _
        rw [show (⟨(x : LQ) * y, hBF (mul_mem x.2 y.2)⟩ : modularFunctionFieldBar (1 * q)) = ⟨x, hBF x.2⟩ * ⟨y, hBF y.2⟩
          from Subtype.ext rfl, map_mul]; rfl)
      map_zero' := Subtype.ext (by
        show ((frickeInvolutionBar (1 * q) ⟨(0 : LQ), _⟩ : modularFunctionFieldBar (1 * q)) : LQ) = 0
        rw [show (⟨(0 : LQ), hBF (zero_mem B)⟩ : modularFunctionFieldBar (1 * q)) = 0 from Subtype.ext rfl, map_zero]; rfl)
      map_add' := fun x y => Subtype.ext (by
        show ((frickeInvolutionBar (1 * q) ⟨(x : LQ) + y, _⟩ : modularFunctionFieldBar (1 * q)) : LQ) = _
        rw [show (⟨(x : LQ) + y, hBF (add_mem x.2 y.2)⟩ : modularFunctionFieldBar (1 * q)) = ⟨x, hBF x.2⟩ + ⟨y, hBF y.2⟩
          from Subtype.ext rfl, map_add]; rfl) }
  let Φ₂ : B →+* modularFunctionFieldC k 1 := (redF red).comp ιw
  let P₁ : Place k (modularFunctionFieldC k 1) := charLGeomPlaceOfPoint k a
  let P₂ : Place k (modularFunctionFieldC k 1) := charLGeomPlaceOfPoint k (a ^ q)
  set S := (IsLocalRing.ResidueField.lift red).fieldRange with hSdef

  have hval : ∀ (x : LQ) (hx : x ∈ Na), ∃ v : k, v ∈ S ∧
      P₁.HasValue (Φ₁ ⟨x, hNaB hx⟩) v ∧ P₂.HasValue (Φ₂ ⟨x, hNaB hx⟩) v := by
    intro x hx
    obtain ⟨h1, h1F, h2, h2F, c, hc1, hc2⟩ :=
      ModularCurve.exists_hasValue_frobNodePair_of_mem_modularLocalizedAtPoint red a ha2 ⟨x, nodeRing_le_field red a hx⟩ hx
    obtain ⟨r, s, hs, hxs⟩ := hx
    have hv1 := hasValue_nodeRing_presentation red a hs hxs h1 h1F
    have hc : c = pointEval A.toSubring red a (a ^ q) r / pointEval A.toSubring red a (a ^ q) s := hc1.unique hv1
    refine ⟨c, ?_, hc1, hc2⟩
    rw [hc]
    exact div_mem (pointEval_mem_fieldRange_lift_red q red a ha2 r) (pointEval_mem_fieldRange_lift_red q red a ha2 s)

  have hmem : ∀ (P : Place k (modularFunctionFieldC k 1)) (Φ : B →+* modularFunctionFieldC k 1),
      (∀ (x : LQ) (hx : x ∈ Na), Φ ⟨x, hNaB hx⟩ ∈ P.toValuationSubring) →
      ∀ x : B, Φ x ∈ P.toValuationSubring := by
    intro P Φ hΦ x
    obtain ⟨p, hp, hpx⟩ := hBint x.1 x.2
    let ψ : ↥Na →+* P.toValuationSubring :=
      { toFun := fun y => ⟨Φ ⟨y, hNaB y.2⟩, hΦ y.1 y.2⟩
        map_one' := Subtype.ext (by show Φ ⟨(1 : LQ), _⟩ = 1; rw [show (⟨(1 : LQ), hNaB (one_mem Na)⟩ : B) = 1 from rfl, map_one])
        map_mul' := fun y z => Subtype.ext (by
          show Φ ⟨(y : LQ) * z, _⟩ = Φ _ * Φ _
          rw [show (⟨(y : LQ) * z, hNaB (mul_mem y.2 z.2)⟩ : B) = ⟨y, hNaB y.2⟩ * ⟨z, hNaB z.2⟩ from rfl, map_mul])
        map_zero' := Subtype.ext (by show Φ ⟨(0 : LQ), _⟩ = 0; rw [show (⟨(0 : LQ), hNaB (zero_mem Na)⟩ : B) = 0 from rfl, map_zero])
        map_add' := fun y z => Subtype.ext (by
          show Φ ⟨(y : LQ) + z, _⟩ = Φ _ + Φ _
          rw [show (⟨(y : LQ) + z, hNaB (add_mem y.2 z.2)⟩ : B) = ⟨y, hNaB y.2⟩ + ⟨z, hNaB z.2⟩ from rfl, map_add]) }
    have h1 : Polynomial.eval₂ (Subring.inclusion hNaB) x p = 0 :=
      Subtype.ext ((Polynomial.hom_eval₂ p (Subring.inclusion hNaB) B.subtype x).trans hpx)
    have hy : IsIntegral P.toValuationSubring (Φ x) := by
      refine ⟨p.map ψ, hp.map ψ, ?_⟩
      have h2 := Polynomial.hom_eval₂ p (Subring.inclusion hNaB) Φ x
      rw [h1, map_zero] at h2
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap (P.toValuationSubring) (modularFunctionFieldC k 1)).comp ψ = Φ.comp (Subring.inclusion hNaB) :=
        RingHom.ext fun y => rfl
      rw [hcomp]; exact h2.symm
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P.toValuationSubring) (K := modularFunctionFieldC k 1)).mp hy
    rw [← hz]; exact z.2
  have hm₁ : ∀ x : B, Φ₁ x ∈ P₁.toValuationSubring :=
    hmem P₁ Φ₁ (fun x hx => by obtain ⟨v, -, hv, -⟩ := hval x hx; exact hv.mem)
  have hm₂ : ∀ x : B, Φ₂ x ∈ P₂.toValuationSubring :=
    hmem P₂ Φ₂ (fun x hx => by obtain ⟨v, -, -, hv⟩ := hval x hx; exact hv.mem)

  have hval_map : ∀ (P : Place k (modularFunctionFieldC k 1)) (hsurj : Function.Surjective (algebraMap k P.ResidueField))
      (Φ : B →+* modularFunctionFieldC k 1) (hm : ∀ x : B, Φ x ∈ P.toValuationSubring),
      ∃ val : B →+* k, ∀ x : B, P.HasValue (Φ x) (val x) := by
    intro P hsurj Φ hm
    let e : k ≃+* P.ResidueField := RingEquiv.ofBijective (algebraMap k P.ResidueField)
      ⟨(algebraMap k P.ResidueField).injective, hsurj⟩
    let χ : B →+* P.toValuationSubring :=
      { toFun := fun x => ⟨Φ x, hm x⟩
        map_one' := Subtype.ext (map_one Φ)
        map_mul' := fun x y => Subtype.ext (map_mul Φ x y)
        map_zero' := Subtype.ext (map_zero Φ)
        map_add' := fun x y => Subtype.ext (map_add Φ x y) }
    refine ⟨e.symm.toRingHom.comp ((IsLocalRing.residue _).comp χ), fun x => ⟨hm x, ?_⟩⟩
    show IsLocalRing.residue P.toValuationSubring (⟨Φ x, hm x⟩ : P.toValuationSubring)
      = algebraMap k P.ResidueField (e.symm (IsLocalRing.residue P.toValuationSubring (χ x)))
    rw [show algebraMap k P.ResidueField (e.symm (IsLocalRing.residue P.toValuationSubring (χ x)))
        = e (e.symm (IsLocalRing.residue P.toValuationSubring (χ x))) from rfl,
      RingEquiv.apply_symm_apply]
    rfl
  obtain ⟨val₁, hv₁⟩ := hval_map P₁ (algebraMap_residueField_charLGeomPlaceOfPoint_surjective k a) Φ₁ hm₁
  obtain ⟨val₂, hv₂⟩ := hval_map P₂ (algebraMap_residueField_charLGeomPlaceOfPoint_surjective k (a ^ q)) Φ₂ hm₂

  have hgen : ∀ r : MvPolynomial (Fin 2) ↥A.toSubring, NodeLocalized.pointEval A.toSubring red a (a ^ q) r = 0 →
      (⟨NodeLocalized.modularEval (1 * q) A.toSubring r,
        hNaB (NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r)⟩ : ↥B) ∈ RingHom.ker val₁ ∧
      (⟨NodeLocalized.modularEval (1 * q) A.toSubring r,
        hNaB (NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r)⟩ : ↥B) ∈ RingHom.ker val₂ := by
    intro r hr
    have hxNa := NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) r
    obtain ⟨v, -, hP1, hP2⟩ := hval _ hxNa
    have hpres : modularEval (1 * q) A.toSubring r * modularEval (1 * q) A.toSubring 1 = modularEval (1 * q) A.toSubring r := by
      rw [map_one, mul_one]
    have h1ne : pointEval A.toSubring red a (a ^ q) 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hv' := hasValue_nodeRing_presentation red a h1ne hpres (hBML (hNaB hxNa)) (Φ₁ ⟨_, hNaB hxNa⟩).2
    have hv0 : v = 0 := by
      have := hP1.unique hv'
      rw [this, hr, zero_div]
    subst hv0
    exact ⟨(RingHom.mem_ker).mpr ((hv₁ _).unique hP1), (RingHom.mem_ker).mpr ((hv₂ _).unique hP2)⟩
  haveI : (RingHom.ker val₁).IsPrime := RingHom.ker_isPrime val₁
  haveI : (RingHom.ker val₂).IsPrime := RingHom.ker_isPrime val₂
  have hker : RingHom.ker val₁ = RingHom.ker val₂ :=
    chart_a_small red a ha ha2 hq B hBF hNaB hBint _ _
      (fun r hr => (hgen r hr).1) (fun r hr => (hgen r hr).2)

  let xf : B := ⟨f, hfB⟩
  have hθ : ∀ y : ↥Na, val₁ (Subring.inclusion hNaB y) ∈ S := fun y => by
    obtain ⟨v, hvS, hP1, -⟩ := hval y.1 y.2
    have : val₁ (Subring.inclusion hNaB y) = v := (hv₁ _).unique hP1
    rw [this]; exact hvS
  have hS : val₁ xf ∈ S := by
    obtain ⟨p, hp, hpx⟩ := hBint _ hfB
    let θ : ↥Na →+* k := val₁.comp (Subring.inclusion hNaB)
    have h1 : Polynomial.eval₂ (Subring.inclusion hNaB) xf p = 0 :=
      Subtype.ext ((Polynomial.hom_eval₂ p (Subring.inclusion hNaB) B.subtype xf).trans hpx)
    have hroot : (p.map θ).eval (val₁ xf) = 0 := by
      rw [Polynomial.eval_map]
      have h2 := Polynomial.hom_eval₂ p (Subring.inclusion hNaB) val₁ xf
      rw [h1, map_zero] at h2; exact h2.symm
    have hlifts : p.map θ ∈ Polynomial.lifts (IsLocalRing.ResidueField.lift red) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨t, ht⟩ := hθ (p.coeff n)
      exact ⟨t, ht⟩
    obtain ⟨P0, hP0map, -, hP0monic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hp.map θ)
    refine mem_fieldRange_lift_red_of_monic q red (val₁ xf) P0 hP0monic ?_
    rw [Polynomial.eval₂_eq_eval_map, hP0map]; exact hroot
  obtain ⟨t, ht⟩ := hS
  obtain ⟨c0, hc0⟩ := IsLocalRing.residue_surjective t

  let cA : ↥A.toSubring := ⟨c0, c0.2⟩
  have hcNa := NodeLocalized.modularEval_mem_modularLocalizedAtPoint (1 * q) A.toSubring red a (a ^ q) (MvPolynomial.C cA)
  let xc : B := ⟨_, hNaB hcNa⟩
  have hvc : val₁ xc = red c0 ∧ val₂ xc = red c0 := by
    obtain ⟨v, -, hP1, hP2⟩ := hval _ hcNa
    have hpres : modularEval (1 * q) A.toSubring (MvPolynomial.C cA) * modularEval (1 * q) A.toSubring 1
        = modularEval (1 * q) A.toSubring (MvPolynomial.C cA) := by rw [map_one, mul_one]
    have h1ne : pointEval A.toSubring red a (a ^ q) 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hv' := hasValue_nodeRing_presentation red a h1ne hpres (hBML (hNaB hcNa)) (Φ₁ ⟨_, hNaB hcNa⟩).2
    have hv0 : v = red c0 := by
      have := hP1.unique hv'
      rw [this, map_one, div_one, pointEval, MvPolynomial.eval₂Hom_C]; rfl
    subst hv0
    exact ⟨(hv₁ _).unique hP1, (hv₂ _).unique hP2⟩
  have hval₁f : val₁ xf = red c0 := by
    rw [← ht, ← hc0, IsLocalRing.ResidueField.lift_residue_apply]
  have hdiff : xf - xc ∈ RingHom.ker val₂ := by
    rw [← hker, RingHom.mem_ker, map_sub, hval₁f, hvc.1, sub_self]
  have hval₂f : val₂ xf = red c0 := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hdiff
    rw [hdiff, hvc.2]
  refine ⟨red c0, ?_, ?_⟩
  · have h := hv₁ xf
    rw [hval₁f] at h
    exact h
  · have h := hv₂ xf
    rw [hval₂f] at h
    exact h

end GLUE
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve.NodeLocalized P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five.ModularCurve"

end S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five
end P2MW
export P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_lt_five (solution)
