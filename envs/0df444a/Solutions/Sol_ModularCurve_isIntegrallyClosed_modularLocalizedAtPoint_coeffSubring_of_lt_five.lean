-- Prove2me | solution 1 for ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/acaa28be-a6b7-5850-a582-67d404ac32be

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Theorems.Thm_ModularCurve_pointEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_isPrime_span_uniformizer_branches_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_phiTwo_eq_mul_add_pow_twelve_mul
import Theorems.Thm_ModularCurve_phiThree_eq_mul_add_pow_six_mul
import Theorems.Thm_ModularCurve_ModularPolynomialData_phi_eq_phiTwo
import Theorems.Thm_ModularCurve_ModularPolynomialData_phi_eq_phiThree
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five.ModularCurve"
open ModularCurve.NodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqNModC jqNModC_one ModularPolynomialData ssJSet phiTwo phiThree pointEval_kroneckerRemainder NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint nonempty_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero phiTwo_eq_mul_add_pow_twelve_mul phiThree_eq_mul_add_pow_six_mul ModularPolynomialData.phi_eq_phiTwo ModularPolynomialData.phi_eq_phiThree eq_zero_of_mem_ssJSet_two eq_zero_of_mem_ssJSet_three"
p2m_open "ModularCurve"
namespace W0SmallAssembly

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

def kronHom (S : Type*) [CommRing S] : Polynomial (Polynomial ℤ) →+* MvPolynomial (Fin 2) S :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom S)) (MvPolynomial.X 0))
    (MvPolynomial.X 1)

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem kronHom_apply (S : Type*) [CommRing S] (R : Polynomial (Polynomial ℤ)) : kronHom S R = kronPoly S R := rfl

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem kronHom_X (S : Type*) [CommRing S] : kronHom S Polynomial.X = MvPolynomial.X 1 := by
  show Polynomial.eval₂ _ _ Polynomial.X = _
  rw [Polynomial.eval₂_X]

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem kronHom_C_X (S : Type*) [CommRing S] : kronHom S (Polynomial.C Polynomial.X) = MvPolynomial.X 0 := by
  show Polynomial.eval₂ _ _ (Polynomial.C Polynomial.X) = _
  rw [Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

omit [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem modularEval_comp_kronHom_C :
    ((modularEval (1 * q) (coeffSubring A K)).comp (kronHom ↥(coeffSubring A K))).comp Polynomial.C
      = (Polynomial.aeval (R := ℤ) (jqNModC Qb 1)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro n
    rw [eq_intCast Polynomial.C n, map_intCast, map_intCast]
  · rw [RingHom.comp_apply, RingHom.comp_apply, kronHom_C_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X, jqNModC_one]
    simp [modularEval]

omit [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem modularEval_comp_kronHom :
    (modularEval (1 * q) (coeffSubring A K)).comp (kronHom ↥(coeffSubring A K))
      = Polynomial.eval₂RingHom (Polynomial.aeval (R := ℤ) (jqNModC Qb 1)).toRingHom (jqNModC Qb (1 * q)) := by
  apply Polynomial.ringHom_ext
  · intro p
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, ← modularEval_comp_kronHom_C (q := q) (A := A) (K := K)]
    rfl
  · rw [RingHom.comp_apply, kronHom_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    simp [modularEval]

omit [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem modularEval_kronHom_phi (data : ModularPolynomialData q) :
    modularEval (1 * q) (coeffSubring A K) (kronHom ↥(coeffSubring A K) data.Φ) = 0 := by
  rw [← RingHom.comp_apply, modularEval_comp_kronHom, Polynomial.coe_eval₂RingHom]
  exact ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero data Qb 1

theorem pointEval_kronHom (P : Polynomial (Polynomial ℤ)) :
    pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (kronHom _ P)
      = ((P.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a := by
  rw [kronHom_apply, ← pointEval_map_incl, map_kronPoly]
  exact ModularCurve.pointEval_kroneckerRemainder (q := q) red P a (a ^ q)

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem span_pair_eq_of_sub_mem {R : Type*} [CommRing R] {p x y : R} (h : x - y ∈ Ideal.span {p}) :
    Ideal.span {p, x} = Ideal.span {p, y} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x ∈ Ideal.span {p, y} := Ideal.mem_span_pair.mpr ⟨c, 1, by linear_combination hc⟩
  have hy : y ∈ Ideal.span {p, x} := Ideal.mem_span_pair.mpr ⟨-c, 1, by linear_combination -hc⟩
  apply le_antisymm
  · exact Ideal.span_le.mpr (Set.insert_subset (Ideal.subset_span (Set.mem_insert _ _)) (Set.singleton_subset_iff.mpr hx))
  · exact Ideal.span_le.mpr (Set.insert_subset (Ideal.subset_span (Set.mem_insert _ _)) (Set.singleton_subset_iff.mpr hy))

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem span_triple_eq_of_sub_mem {R : Type*} [CommRing R] {p x y x' y' : R}
    (hx : x - x' ∈ Ideal.span {p}) (hy : y - y' ∈ Ideal.span {p}) :
    Ideal.span {p, x, y} = Ideal.span {p, x', y'} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hy
  have key : ∀ {u v u' v' : R} (cu cv : R), cu * p = u - u' → cv * p = v - v' →
      Ideal.span {p, u, v} ≤ Ideal.span {p, u', v'} := by
    intro u v u' v' cu cv hu hv
    refine Ideal.span_le.mpr (Set.insert_subset (Ideal.subset_span (Set.mem_insert _ _))
      (Set.insert_subset ?_ (Set.singleton_subset_iff.mpr ?_)))
    · exact Ideal.mem_span_insert.mpr ⟨cu, u', Ideal.subset_span (Set.mem_insert _ _), by linear_combination -hu⟩
    · exact Ideal.mem_span_insert.mpr ⟨cv, v', Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)),
        by linear_combination -hv⟩
  exact le_antisymm (key c d hc hd) (key (-c) (-d) (by linear_combination -hc) (by linear_combination -hd))

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem span_pair_neg {R : Type*} [CommRing R] (p x : R) : Ideal.span {p, -x} = Ideal.span {p, x} := by
  rw [Ideal.span_insert, Ideal.span_singleton_neg, ← Ideal.span_insert]

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in
theorem span_triple_neg {R : Type*} [CommRing R] (p x y : R) : Ideal.span {p, -x, y} = Ideal.span {p, x, y} := by
  rw [Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_neg, ← Ideal.span_insert, ← Ideal.span_insert]

theorem stepDE_of_widthPresentation
    (Φ g h r γ δ : Polynomial (Polynomial ℤ)) (e : ℕ)
    (hΦ0 : modularEval (1 * q) (coeffSubring A K) (kronHom _ Φ) = 0)
    (hid : Φ = g * h + (q : Polynomial (Polynomial ℤ)) ^ e * r)
    (hg : g = Polynomial.C Polynomial.X ^ q - Polynomial.X + (q : Polynomial (Polynomial ℤ)) * γ)
    (hh : h = Polynomial.C Polynomial.X - Polynomial.X ^ q + (q : Polynomial (Polynomial ℤ)) * δ)
    (hr : ((r.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a ≠ 0) :
    ∃ G' H' U : ↥(R₀ q A red a K), IsUnit U ∧
      G' * H' = ev q A red a K (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) ^ e * U ∧
      G' + ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)
        = ev q A red a K (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) * ev q A red a K (kronHom _ γ) ∧
      H' - ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
        = ev q A red a K (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) * ev q A red a K (kronHom _ δ) := by
  classical
  have hq' : kronHom ↥(coeffSubring A K) (q : Polynomial (Polynomial ℤ)) = MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K)) := by
    rw [map_natCast, map_natCast]
  have hG : kronHom ↥(coeffSubring A K) g = -(MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)
      + MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K)) * kronHom _ γ := by
    rw [hg, map_add, map_sub, map_mul, map_pow, kronHom_C_X, kronHom_X, hq']; ring
  have hH : kronHom ↥(coeffSubring A K) h = (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
      + MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K)) * kronHom _ δ := by
    rw [hh, map_add, map_sub, map_mul, map_pow, kronHom_C_X, kronHom_X, hq']
  have hΦ : kronHom ↥(coeffSubring A K) Φ = kronHom _ g * kronHom _ h
      + MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K)) ^ e * kronHom _ r := by
    rw [hid, map_add, map_mul, map_mul, map_pow, hq']

  have hne : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) (kronHom _ r) ≠ 0 := by
    rw [pointEval_kronHom]; exact hr
  have hR0 : modularEval (1 * q) (coeffSubring A K) (kronHom _ r) ≠ 0 := fun h0 =>
    hne (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K _ h0)
  have hU : IsUnit (ev q A red a K (kronHom _ r)) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(modularEval (1 * q) (coeffSubring A K) (kronHom _ r))⁻¹, 1, kronHom _ r, hne, ?_⟩, ?_⟩
    · rw [map_one]; exact inv_mul_cancel₀ hR0
    · exact Subtype.ext (mul_inv_cancel₀ hR0)
  refine ⟨ev q A red a K (kronHom _ g), ev q A red a K (kronHom _ h), -ev q A red a K (kronHom _ r), hU.neg, ?_, ?_, ?_⟩
  · have h0 : ev q A red a K (kronHom _ Φ) = 0 := Subtype.ext hΦ0
    rw [hΦ, ← evHom_apply, map_add, map_mul, map_mul, map_pow] at h0
    rw [← evHom_apply, ← evHom_apply, ← evHom_apply, ← evHom_apply, mul_neg]
    exact eq_neg_of_add_eq_zero_left h0
  · rw [hG, ← evHom_apply, ← evHom_apply, ← evHom_apply, ← evHom_apply, map_add, map_neg, map_mul]; ring
  · rw [hH, ← evHom_apply, ← evHom_apply, ← evHom_apply, ← evHom_apply, map_add, map_mul]; ring

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem widthPresentation_two :
    ∃ g h r γ δ : Polynomial (Polynomial ℤ),
      phiTwo = g * h + (2 : Polynomial (Polynomial ℤ)) ^ 12 * r ∧
      g = Polynomial.C Polynomial.X ^ 2 - Polynomial.X + (2 : Polynomial (Polynomial ℤ)) * γ ∧
      h = Polynomial.C Polynomial.X - Polynomial.X ^ 2 + (2 : Polynomial (Polynomial ℤ)) * δ ∧
      ¬ ((2 : ℤ) ∣ (r.eval (Polynomial.C 0)).eval 0) := by
  refine ⟨_, _, _, 1304 * Polynomial.C Polynomial.X + 384, 744 * Polynomial.X + 1664,
    ModularCurve.phiTwo_eq_mul_add_pow_twelve_mul, by ring, by ring, ?_⟩
  norm_num [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_C, Polynomial.eval_X]

omit [Fact q.Prime] [CharP k q] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem widthPresentation_three :
    ∃ g h r γ δ : Polynomial (Polynomial ℤ),
      phiThree = g * h + (3 : Polynomial (Polynomial ℤ)) ^ 6 * r ∧
      g = Polynomial.C Polynomial.X ^ 3 - Polynomial.X + (3 : Polynomial (Polynomial ℤ)) * γ ∧
      h = Polynomial.C Polynomial.X - Polynomial.X ^ 3 + (3 : Polynomial (Polynomial ℤ)) * δ ∧
      ¬ ((3 : ℤ) ∣ (r.eval (Polynomial.C 0)).eval 0) := by
  refine ⟨_, _, _, 228 * Polynomial.C Polynomial.X ^ 2 + 171 * Polynomial.C Polynomial.X + 9,
    15 * Polynomial.X ^ 2 + 72 * Polynomial.X + 234,
    ModularCurve.phiThree_eq_mul_add_pow_six_mul, by ring, by ring, ?_⟩
  norm_num [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_C, Polynomial.eval_X]

omit [Fact q.Prime] [DecidableEq k] [FiniteDimensional ℚ K] in

theorem eval_eval_map_intCast (P : Polynomial (Polynomial ℤ)) (x y : ℤ) :
    ((P.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C ((x : ℤ) : k))).eval ((y : ℤ) : k)
      = (((P.eval (Polynomial.C x)).eval y : ℤ) : k) := by
  have h1 : Polynomial.C ((x : ℤ) : k) = Polynomial.mapRingHom (Int.castRingHom k) (Polynomial.C x) := by
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, eq_intCast]
  rw [h1, Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.coe_mapRingHom, ← eq_intCast (Int.castRingHom k) y,
    Polynomial.eval_map, Polynomial.eval₂_hom, eq_intCast]

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

section Main
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]

theorem stepG_of_widthPresentation (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K] (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (Φ g h r γ δ : Polynomial (Polynomial ℤ)) (e : ℕ) (he : 1 ≤ e)
    (hΦ0 : modularEval (1 * q) (coeffSubring A K) (kronHom _ Φ) = 0)
    (hid : Φ = g * h + (q : Polynomial (Polynomial ℤ)) ^ e * r)
    (hg : g = Polynomial.C Polynomial.X ^ q - Polynomial.X + (q : Polynomial (Polynomial ℤ)) * γ)
    (hh : h = Polynomial.C Polynomial.X - Polynomial.X ^ q + (q : Polynomial (Polynomial ℤ)) * δ)
    (hr : ((r.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a ≠ 0) :
    IsIntegrallyClosed ↥(R₀ q A red a K) := by
  classical
  obtain ⟨ϖ, hϖirr, hϖ, eK, ε, heK, hε, hqe⟩ := stepA_uniformizer red K q
  obtain ⟨hnoeth, hloc, -, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hnoeth; haveI := hloc
  obtain ⟨⟨hPG, hHG, -⟩, hbr2⟩ :=
    ModularCurve.NodeLocalized.isPrime_span_uniformizer_branches_modularLocalizedAtPoint red a K ϖ hϖ
  obtain ⟨hPH, hGH⟩ := hbr2 ha2
  obtain ⟨G', H', U, hU, hGH', hG', hH'⟩ :=
    stepDE_of_widthPresentation red a K Φ g h r γ δ e hΦ0 hid hg hh hr
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := stepA_dvr red K q
  letI : Algebra ↥(coeffSubring A K) ↥(R₀ q A red a K) := (constHom q A red a K).toAlgebra
  have halg : ∀ c, algebraMap ↥(coeffSubring A K) ↥(R₀ q A red a K) c = ev q A red a K (MvPolynomial.C c) :=
    fun c => rfl

  have hqR : ev q A red a K (MvPolynomial.C ((q : ℕ) : ↥(coeffSubring A K))) = ev q A red a K (MvPolynomial.C ϖ) ^ eK * ev q A red a K (MvPolynomial.C ε) := by
    rw [hqe, ← evHom_apply, ← evHom_apply, ← evHom_apply, map_mul, map_pow, map_mul, map_pow]

  have hG'mem : G' - (-ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)) ∈ Ideal.span {ev q A red a K (MvPolynomial.C ϖ)} := by
    rw [sub_neg_eq_add, hG', hqR, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ heK)
  have hH'mem : H' - ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) ∈ Ideal.span {ev q A red a K (MvPolynomial.C ϖ)} := by
    rw [hH', hqR, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ heK)
  have hspanG : Ideal.span {ev q A red a K (MvPolynomial.C ϖ), G'} = Ideal.span {ev q A red a K (MvPolynomial.C ϖ), ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} :=
    (span_pair_eq_of_sub_mem hG'mem).trans (span_pair_neg _ _)
  have hspanH : Ideal.span {ev q A red a K (MvPolynomial.C ϖ), H'} = Ideal.span {ev q A red a K (MvPolynomial.C ϖ), ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)} := span_pair_eq_of_sub_mem hH'mem
  have hspanM : Ideal.span {ev q A red a K (MvPolynomial.C ϖ), G', H'} = Ideal.span {ev q A red a K (MvPolynomial.C ϖ), ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q), ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)} :=
    (span_triple_eq_of_sub_mem hG'mem hH'mem).trans (span_triple_neg _ _ _)
  have hsub : Ideal.span {ev q A red a K (MvPolynomial.C ϖ)} ≤ Ideal.span {ev q A red a K (MvPolynomial.C ϖ), ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)} := Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hsub' : Ideal.span {ev q A red a K (MvPolynomial.C ϖ)} ≤ Ideal.span {ev q A red a K (MvPolynomial.C ϖ), ev q A red a K (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)} := Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  refine IsLocalRing.isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit ϖ hϖirr
    (stepF_residue_surjective red a K x hx) G' H' (ev q A red a K (MvPolynomial.C ε) ^ e * U)
    (((hε.map (constHom q A red a K)).pow e).mul hU) (e * eK)
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp he) (Nat.one_le_iff_ne_zero.mp heK)))
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hGH', hqR, halg, mul_pow, ← pow_mul, mul_comm e eK, mul_assoc]
  · rw [halg, hspanM]; exact stepC_maximalIdeal_eq red a K ha2 ϖ hϖ x hx hmax
  · rw [halg, hspanG]; exact hPG
  · rw [halg, hspanH]; exact hPH
  · rw [halg, hspanG]
    intro hmem
    apply hHG
    have h1 := Ideal.sub_mem _ hmem (hsub hH'mem)
    rwa [sub_sub_cancel] at h1
  · rw [halg, hspanH]
    intro hmem
    apply hGH
    have h1 := Ideal.sub_mem _ (hsub' hG'mem) hmem
    have h2 : G' - -ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) - G' = ev q A red a K (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) := by ring
    rwa [h2] at h1

theorem _root_.P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five.solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (hq : q < 5)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
  classical
  obtain ⟨x, hx⟩ := hx
  have hprime : q.Prime := Fact.out
  have hq23 : q = 2 ∨ q = 3 := by
    interval_cases q
    · exact absurd hprime (by decide)
    · exact absurd hprime (by decide)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hprime (by decide)
  rcases hq23 with rfl | rfl
  ·
    have ha0 : a = 0 := ModularCurve.eq_zero_of_mem_ssJSet_two a ha ha2
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData 2
    obtain ⟨g, h, r, γ, δ, hid, hg, hh, hr⟩ := widthPresentation_two
    have hΦ0 : modularEval (1 * 2) (coeffSubring A K) (kronHom _ phiTwo) = 0 := by
      rw [← ModularCurve.ModularPolynomialData.phi_eq_phiTwo data]; exact modularEval_kronHom_phi K data
    refine stepG_of_widthPresentation red a ha2 K x hx phiTwo g h r γ δ 12 (by norm_num) hΦ0
      (by exact_mod_cast hid) (by exact_mod_cast hg) (by exact_mod_cast hh) ?_
    subst ha0
    have hv := eval_eval_map_intCast (k := k) r 0 0
    simp only [Int.cast_zero] at hv
    rw [zero_pow two_ne_zero, hv, Ne, CharP.intCast_eq_zero_iff k 2]
    exact hr
  ·
    have ha0 : a = 0 := ModularCurve.eq_zero_of_mem_ssJSet_three a ha ha2
    obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData 3
    obtain ⟨g, h, r, γ, δ, hid, hg, hh, hr⟩ := widthPresentation_three
    have hΦ0 : modularEval (1 * 3) (coeffSubring A K) (kronHom _ phiThree) = 0 := by
      rw [← ModularCurve.ModularPolynomialData.phi_eq_phiThree data]; exact modularEval_kronHom_phi K data
    refine stepG_of_widthPresentation red a ha2 K x hx phiThree g h r γ δ 6 (by norm_num) hΦ0
      (by exact_mod_cast hid) (by exact_mod_cast hg) (by exact_mod_cast hh) ?_
    subst ha0
    have hv := eval_eval_map_intCast (k := k) r 0 0
    simp only [Int.cast_zero] at hv
    rw [zero_pow three_ne_zero, hv, Ne, CharP.intCast_eq_zero_iff k 3]
    exact hr

end Main

end W0SmallAssembly
end ModularCurve

end

end S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five
end P2MW
export P2MW.S_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five (solution)
