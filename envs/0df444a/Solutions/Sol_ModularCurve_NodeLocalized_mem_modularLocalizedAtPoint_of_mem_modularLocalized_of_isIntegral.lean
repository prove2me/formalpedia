-- Prove2me | solution 1 for ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2a61b2fe-7c15-53d7-a2a7-49b405f279e4

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ModularCurve_modularRing_eq_range_modularEval
import Theorems.Thm_ModularCurve_redRes_modularEval
import Theorems.Thm_ModularCurve_isPrime_span_uniformizer_and_maximalIdeal_modularLocalizedAtPoint_eq_of_pow_sq_ne
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.NodeLocalized.coe_modularEvalAt"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral.ModularCurve"
open ModularCurve.NodeLocalized ModularCurve.CharPReduction

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.redRes CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc_coe CharPReduction.modularLocalized CharPReduction.modularRedLocHom jqModC jqNModC qExpand_congr ModularPolynomialData KroneckerCongruence frobenius_identity_geom_unconditional modularRing_eq_range_modularEval redRes_modularEval isPrime_span_uniformizer_and_maximalIdeal_modularLocalizedAtPoint_eq_of_pow_sq_ne isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing transcendental_jqModC"
p2m_open "ModularCurve"
namespace RegG

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

section Incl
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q] [DecidableEq k]
variable (red : A →+* k) (a : k) (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]

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

end Incl

section Kron
variable (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q]

theorem jqNModC_one_mul_eq_pow : jqNModC k (1 * q) = jqModC k ^ q := by
  rw [show jqNModC k (1 * q) = jqNModC k q from qExpand_congr (one_mul q) _]
  exact frobenius_identity_geom_unconditional k

end Kron

namespace NodeLocalized
section OneVar
variable (q : ℕ) {A : Type*} [CommRing A] {k : Type*} [Field k] (red : A →+* k)

noncomputable def nodePoly : MvPolynomial (Fin 2) A →+* Polynomial k :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]

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
end NodeLocalized

section Plumbing
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]
variable (red : A →+* k) (K : IntermediateField ℚ Qb)

theorem exists_map_incl_eq (P : MvPolynomial (Fin 2) ↥A.toSubring)
    (hP : ∀ m, ((P.coeff m : ↥A.toSubring) : Qb) ∈ K) :
    ∃ P₀ : MvPolynomial (Fin 2) ↥(coeffSubring A K), MvPolynomial.map (incl A K) P₀ = P := by
  classical
  refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m ⟨((P.coeff m : ↥A.toSubring) : Qb), (P.coeff m).2, hP m⟩, ?_⟩
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum P]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial]
  rfl

theorem modularEvalRed_map_incl (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![jqModC k, jqNModC k (1 * q)]
        (MvPolynomial.map (incl A K) r)
      = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp (redRestrict red K)) ![jqModC k, jqNModC k (1 * q)] r := by
  rw [MvPolynomial.eval₂Hom_map_hom]
  rfl

theorem modularEvalRed_ne_zero_of_pointEval_ne_zero (a : k) (s : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0) :
    MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp (redRestrict red K)) ![jqModC k, jqNModC k (1 * q)] s ≠ 0 := by
  have h1 : MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp (redRestrict red K)) ![jqModC k, jqNModC k (1 * q)] s
      = Polynomial.aeval (jqModC k) (NodeLocalized.nodePoly q (redRestrict red K) s) := by
    rw [NodeLocalized.aeval_nodePoly, ← jqNModC_one_mul_eq_pow q k]
  have hne : NodeLocalized.nodePoly q (redRestrict red K) s ≠ 0 := by
    intro h0
    apply hs
    have := NodeLocalized.eval_nodePoly q (redRestrict red K) s a
    rw [h0, Polynomial.eval_zero] at this
    rw [pointEval]
    exact this.symm
  rw [h1]
  intro h0
  exact transcendental_jqModC k ⟨NodeLocalized.nodePoly q (redRestrict red K) s, hne, h0⟩

include q red in

theorem exists_pow_mul_mem [FiniteDimensional ℚ K] (ϖ : ↥(coeffSubring A K))
    (hϖ : Irreducible ϖ) (c : Qb) (hc : c ∈ K) :
    ∃ m : ℕ, ((ϖ : Qb) ^ m * c) ∈ coeffSubring A K := by
  classical
  haveI := stepA_dvr red K q
  rcases A.mem_or_inv_mem c with hcA | hcA
  · exact ⟨0, by rw [pow_zero, one_mul]; exact ⟨hcA, hc⟩⟩
  · by_cases hc0 : c = 0
    · exact ⟨0, by rw [hc0, mul_zero]; exact zero_mem _⟩
    · have hinv : (⟨c⁻¹, hcA, K.inv_mem hc⟩ : ↥(coeffSubring A K)) ≠ 0 := by
        intro h; apply hc0
        have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h
        simpa using this
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hinv hϖ
      refine ⟨n, ?_⟩
      have e : (ϖ : Qb) ^ n * c = (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) := by
        have h1 : (c⁻¹ : Qb) = ((u : ↥(coeffSubring A K)) : Qb) * (ϖ : Qb) ^ n := by
          have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) hu
          push_cast at this
          exact this
        have h2 : (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) * ((u : ↥(coeffSubring A K)) : Qb) = 1 := by
          have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) u.inv_mul
          push_cast at this
          exact this
        have h3 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
        calc (ϖ : Qb) ^ n * c = (ϖ : Qb) ^ n * c * ((((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) * ((u : ↥(coeffSubring A K)) : Qb)) := by rw [h2, mul_one]
          _ = (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) * (c * (((u : ↥(coeffSubring A K)) : Qb) * (ϖ : Qb) ^ n)) := by ring
          _ = (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) := by rw [← h1, h3, mul_one]
      rw [e]
      exact ((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)).2

end Plumbing

section Main
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]

set_option maxHeartbeats 16000000 in

theorem mainRegG (red : A →+* k)
    (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (g : LQ) (hg : g ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hint : IsIntegral (Algebra.adjoin Qb {jqModC Qb}) g)
    (x₀ : A) (hb : red x₀ ^ (q ^ 2) ≠ red x₀) :
    g ∈ modularLocalizedAtPoint (1 * q) A.toSubring red (red x₀) (red x₀ ^ q) := by
  classical
  letI : DecidableEq k := Classical.decEq k

  obtain ⟨r, s, hs, hgs⟩ := (CharPReduction.mem_localizedAtKer _ _ _ _).mp hg
  obtain ⟨Pr, hPr⟩ : (r : LQ) ∈ (modularEval (1 * q) A.toSubring).range := by
    rw [← ModularCurve.modularRing_eq_range_modularEval]; exact r.2
  obtain ⟨Ps, hPs⟩ : (s : LQ) ∈ (modularEval (1 * q) A.toSubring).range := by
    rw [← ModularCurve.modularRing_eq_range_modularEval]; exact s.2
  have hs0 : (s : LQ) ≠ 0 := by
    intro h0; apply hs
    have : s = 0 := Subtype.ext h0
    rw [this]; exact Ideal.zero_mem _
  have hsred : CharPReduction.redRes A.toSubring red (modularRing (1 * q) A.toSubring) (modularRing_le_integralCoeffs (1 * q) A.toSubring) s ≠ 0 :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mp hs

  obtain ⟨p, hpmonic, hp⟩ := hint
  set n := p.natDegree with hn_def
  have hcoef : ∀ i : ℕ, ∃ b : Polynomial Qb, Polynomial.aeval (jqModC Qb) b = ((p.coeff i : Algebra.adjoin Qb {jqModC Qb}) : LQ) := by
    intro i
    have hm : ((p.coeff i : Algebra.adjoin Qb {jqModC Qb}) : LQ) ∈ Algebra.adjoin Qb {jqModC Qb} := (p.coeff i).2
    have hm' := (SetLike.ext_iff.mp (Algebra.adjoin_singleton_eq_range_aeval Qb (jqModC Qb)) _).mp hm
    exact (AlgHom.mem_range _).mp hm'
  choose b hbq using hcoef
  have heq : g ^ n + ∑ i ∈ Finset.range n, Polynomial.aeval (jqModC Qb) (b i) * g ^ i = 0 := by
    have h1 : p.eval₂ (algebraMap (Algebra.adjoin Qb {jqModC Qb}) LQ) g = 0 := hp
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, ← hn_def] at h1
    have hlead : (algebraMap (Algebra.adjoin Qb {jqModC Qb}) LQ) (p.coeff n) = 1 := by
      rw [hn_def, Polynomial.coeff_natDegree, hpmonic.leadingCoeff, map_one]
    rw [hlead, one_mul, add_comm] at h1
    rw [← h1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbq i]
    rfl

  set S : Finset Qb := insert (x₀ : Qb)
    ((Pr.support.image fun m => ((Pr.coeff m : ↥A.toSubring) : Qb)) ∪ (Ps.support.image fun m => ((Ps.coeff m : ↥A.toSubring) : Qb))
      ∪ (Finset.range n).biUnion fun i => (b i).support.image fun j => (b i).coeff j) with hS
  set K : IntermediateField ℚ Qb := IntermediateField.adjoin ℚ (S : Set Qb) with hK
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  have hSK : ∀ x ∈ S, x ∈ K := fun x hx => IntermediateField.subset_adjoin ℚ _ (Finset.mem_coe.mpr hx)
  have hx₀K : (x₀ : Qb) ∈ K := hSK _ (Finset.mem_insert_self _ _)
  have hPrK : ∀ m, ((Pr.coeff m : ↥A.toSubring) : Qb) ∈ K := by
    intro m
    by_cases hm : m ∈ Pr.support
    · exact hSK _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm))))
    · rw [MvPolynomial.notMem_support_iff.mp hm]; exact zero_mem _
  have hPsK : ∀ m, ((Ps.coeff m : ↥A.toSubring) : Qb) ∈ K := by
    intro m
    by_cases hm : m ∈ Ps.support
    · exact hSK _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm))))
    · rw [MvPolynomial.notMem_support_iff.mp hm]; exact zero_mem _
  have hbK : ∀ i ∈ Finset.range n, ∀ j, (b i).coeff j ∈ K := by
    intro i hi j
    by_cases hj : j ∈ (b i).support
    · exact hSK _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image_of_mem _ hj⟩)))
    · rw [Polynomial.notMem_support_iff.mp hj]; exact zero_mem _
  set a : k := red x₀ with ha_def
  set x : ↥(coeffSubring A K) := ⟨(x₀ : Qb), x₀.2, hx₀K⟩ with hx_def
  have hx : redRestrict red K x = a := by
    show red (Subring.inclusion _ x) = red x₀
    congr 1

  obtain ⟨Pr₀, hPr₀⟩ := exists_map_incl_eq K Pr hPrK
  obtain ⟨Ps₀, hPs₀⟩ := exists_map_incl_eq K Ps hPsK
  have hPr₀v : modularEval (1 * q) (coeffSubring A K) Pr₀ = r := by rw [← modularEval_map_incl, hPr₀, hPr]
  have hPs₀v : modularEval (1 * q) (coeffSubring A K) Ps₀ = s := by rw [← modularEval_map_incl, hPs₀, hPs]

  obtain ⟨ϖ, hϖirr, hϖ, -⟩ := stepA_uniformizer red K q
  obtain ⟨hnoeth, hloc, -, -⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hnoeth
  haveI := hloc
  have hba : a ^ (q ^ 2) ≠ a := hb
  obtain ⟨hprime, -⟩ :=
    ModularCurve.isPrime_span_uniformizer_and_maximalIdeal_modularLocalizedAtPoint_eq_of_pow_sq_ne red a hba K x hx ϖ hϖ
  have hic : IsIntegrallyClosed ↥(R₀ q A red a K) :=
    ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne red a hba K x hx
  set cϖ : ↥(R₀ q A red a K) := ev q A red a K (MvPolynomial.C ϖ) with hcϖ
  change (Ideal.span {cϖ}).IsPrime at hprime
  have hϖ0 : (ϖ : Qb) ≠ 0 := fun h => hϖirr.ne_zero (Subtype.ext h)
  have hcϖval : ((cϖ : ↥(R₀ q A red a K)) : LQ) = algebraMap Qb LQ (ϖ : Qb) := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ) = _
    rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    rfl
  have hcϖ0 : cϖ ≠ 0 := by
    intro h
    have h1 : algebraMap Qb LQ (ϖ : Qb) = 0 := by rw [← hcϖval, h]; rfl
    exact hϖ0 ((map_eq_zero_iff _ (algebraMap Qb LQ).injective).mp h1)

  have hle : R₀ q A red a K ≤ CharPReduction.modularLocalized (1 * q) (coeffSubring A K) (redRestrict red K) := by
    rintro f ⟨r', s', hs', e⟩
    refine (CharPReduction.mem_localizedAtKer _ _ _ _).mpr
      ⟨⟨modularEval (1 * q) (coeffSubring A K) r', by rw [ModularCurve.modularRing_eq_range_modularEval]; exact ⟨r', rfl⟩⟩,
       ⟨modularEval (1 * q) (coeffSubring A K) s', by rw [ModularCurve.modularRing_eq_range_modularEval]; exact ⟨s', rfl⟩⟩, ?_, e⟩
    rw [CharPReduction.notMem_redKer_iff, ModularCurve.redRes_modularEval]
    exact modularEvalRed_ne_zero_of_pointEval_ne_zero red K a s' hs'
  set ρ : ↥(R₀ q A red a K) →+* LaurentSeries k :=
    (CharPReduction.modularRedLocHom (1 * q) (coeffSubring A K) (redRestrict red K)).comp (Subring.inclusion hle) with hρ
  have hρev : ∀ P : MvPolynomial (Fin 2) ↥(coeffSubring A K), ρ (ev q A red a K P)
      = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp (redRestrict red K)) ![jqModC k, jqNModC k (1 * q)] P := by
    intro P
    have hmem : modularEval (1 * q) (coeffSubring A K) P ∈ modularRing (1 * q) (coeffSubring A K) := by
      rw [ModularCurve.modularRing_eq_range_modularEval]; exact ⟨P, rfl⟩
    rw [← ModularCurve.redRes_modularEval (1 * q) (coeffSubring A K) (redRestrict red K) P hmem]
    exact CharPReduction.redLoc_coe (⟨modularEval (1 * q) (coeffSubring A K) P, hmem⟩ : ↥(modularRing (1 * q) (coeffSubring A K)))
  have hρϖ : ρ cϖ = 0 := by
    rw [hcϖ, hρev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply,
      (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩, map_zero]
  have hρs : ρ (ev q A red a K Ps₀) ≠ 0 := by
    rw [hρev, ← modularEvalRed_map_incl, hPs₀]
    have hmem : modularEval (1 * q) A.toSubring Ps ∈ modularRing (1 * q) A.toSubring := by
      rw [ModularCurve.modularRing_eq_range_modularEval]; exact ⟨Ps, rfl⟩
    rw [← ModularCurve.redRes_modularEval (1 * q) A.toSubring red Ps hmem]
    have e : (⟨modularEval (1 * q) A.toSubring Ps, hmem⟩ : ↥(modularRing (1 * q) A.toSubring)) = s := Subtype.ext hPs
    rw [e]; exact hsred
  have hs_notMem : ev q A red a K Ps₀ ∉ Ideal.span {cϖ} := by
    intro hmem
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    apply hρs
    rw [← hw, map_mul, hρϖ, mul_zero]

  have hM : ∃ M : ℕ, ∀ i ∈ Finset.range n, ∀ j, ((ϖ : Qb) ^ M * (b i).coeff j) ∈ coeffSubring A K := by
    have hfin : ∀ i ∈ Finset.range n, ∃ Mi : ℕ, ∀ j, ((ϖ : Qb) ^ Mi * (b i).coeff j) ∈ coeffSubring A K := by
      intro i hi
      have hj : ∀ j, ∃ m : ℕ, ((ϖ : Qb) ^ m * (b i).coeff j) ∈ coeffSubring A K := fun j =>
        exists_pow_mul_mem (q := q) red K ϖ hϖirr _ (hbK i hi j)
      choose m hm using hj
      refine ⟨(b i).support.sup m, fun j => ?_⟩
      by_cases hjs : j ∈ (b i).support
      · have hle' : m j ≤ (b i).support.sup m := Finset.le_sup hjs
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle'
        rw [hd, pow_add, mul_comm ((ϖ : Qb) ^ m j), mul_assoc]
        exact mul_mem (pow_mem ϖ.2 d) (hm j)
      · rw [Polynomial.notMem_support_iff.mp hjs, mul_zero]; exact zero_mem _
    choose! Mi hMi using hfin
    refine ⟨(Finset.range n).sup Mi, fun i hi j => ?_⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := Mi) hi)
    rw [hd, pow_add, mul_comm ((ϖ : Qb) ^ Mi i), mul_assoc]
    exact mul_mem (pow_mem ϖ.2 d) (hMi i hi j)
  obtain ⟨M, hM⟩ := hM

  have hcoefR : ∀ i ∈ Finset.range n,
      algebraMap Qb LQ ((ϖ : Qb) ^ M) * Polynomial.aeval (jqModC Qb) (b i) ∈ R₀ q A red a K := by
    intro i hi

    set Q : MvPolynomial (Fin 2) ↥(coeffSubring A K) :=
      ∑ j ∈ Finset.range ((b i).natDegree + 1), MvPolynomial.monomial (Finsupp.single 0 j) ⟨(ϖ : Qb) ^ M * (b i).coeff j, hM i hi j⟩ with hQ
    have hQv : modularEval (1 * q) (coeffSubring A K) Q = algebraMap Qb LQ ((ϖ : Qb) ^ M) * Polynomial.aeval (jqModC Qb) (b i) := by
      rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, hQ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, Finsupp.prod_single_index, pow_zero,
        Matrix.cons_val_zero, Algebra.smul_def]
      show algebraMap Qb LQ ((ϖ : Qb) ^ M * (b i).coeff j) * (jqModC Qb) ^ j = _
      rw [map_mul]
      ring
    rw [← hQv]
    exact (ev q A red a K Q).2

  have hinj : Function.Injective (algebraMap ↥(R₀ q A red a K) LQ) := Subtype.val_injective
  let φ : FractionRing ↥(R₀ q A red a K) →ₐ[↥(R₀ q A red a K)] LQ :=
    { IsFractionRing.lift hinj with commutes' := fun r => IsFractionRing.lift_algebraMap hinj r }
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hφalg : ∀ z : ↥(R₀ q A red a K), φ (algebraMap ↥(R₀ q A red a K) (FractionRing ↥(R₀ q A red a K)) z) = (z : LQ) := fun z => IsFractionRing.lift_algebraMap hinj z
  have hevs0 : ev q A red a K Ps₀ ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥(R₀ q A red a K) => (z : LQ)) h
    apply hs0
    rw [← hPs₀v]; exact this
  have halgs0 : algebraMap ↥(R₀ q A red a K) (FractionRing ↥(R₀ q A red a K)) (ev q A red a K Ps₀) ≠ 0 :=
    fun h => hevs0 (IsFractionRing.injective ↥(R₀ q A red a K) (FractionRing ↥(R₀ q A red a K)) (by rw [h, map_zero]))
  set f : FractionRing ↥(R₀ q A red a K) := algebraMap ↥(R₀ q A red a K) _ (ev q A red a K Pr₀) / algebraMap ↥(R₀ q A red a K) _ (ev q A red a K Ps₀) with hf
  have hφf : φ f = g := by
    rw [hf, map_div₀, hφalg, hφalg]
    show modularEval (1 * q) (coeffSubring A K) Pr₀ / modularEval (1 * q) (coeffSubring A K) Ps₀ = g
    rw [hPr₀v, hPs₀v, div_eq_iff hs0, hgs]
  have hv : ∃ r' s' : ↥(R₀ q A red a K), s' ∉ Ideal.span {cϖ} ∧ f * algebraMap ↥(R₀ q A red a K) (FractionRing ↥(R₀ q A red a K)) s' = algebraMap ↥(R₀ q A red a K) (FractionRing ↥(R₀ q A red a K)) r' :=
    ⟨ev q A red a K Pr₀, ev q A red a K Ps₀, hs_notMem, by rw [hf, div_mul_cancel₀ _ halgs0]⟩
  have hintR : ∃ N : ℕ, IsIntegral ↥(R₀ q A red a K) (algebraMap ↥(R₀ q A red a K) (FractionRing ↥(R₀ q A red a K)) cϖ ^ N * f) := by
    refine ⟨M, ?_⟩
    rw [← isIntegral_algHom_iff φ hφ, map_mul, map_pow, hφalg, hφf, hcϖval, ← map_pow]

    set ϖc : LQ := algebraMap Qb LQ ((ϖ : Qb) ^ M) with hϖc
    set G : LQ := ϖc * g with hG
    have hC : ∀ i ∈ Finset.range n, ϖc ^ (n - i) * Polynomial.aeval (jqModC Qb) (b i) ∈ R₀ q A red a K := by
      intro i hi
      have hlt : i < n := Finset.mem_range.mp hi
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
      rw [hd, show i + d + 1 - i = d + 1 by omega, pow_succ, mul_assoc]
      refine mul_mem (pow_mem ?_ d) (hcoefR i hi)
      rw [hϖc, map_pow]
      exact pow_mem (hcϖval ▸ cϖ.2) M
    let C : Fin n → ↥(R₀ q A red a K) := fun i => ⟨ϖc ^ (n - (i : ℕ)) * Polynomial.aeval (jqModC Qb) (b i), hC i (Finset.mem_range.mpr i.2)⟩
    have hGeq : G ^ n + ∑ i : Fin n, (C i : LQ) * G ^ (i : ℕ) = 0 := by
      have key : ∀ i : Fin n, (C i : LQ) * G ^ (i : ℕ) = ϖc ^ n * (Polynomial.aeval (jqModC Qb) (b i) * g ^ (i : ℕ)) := by
        intro i
        show ϖc ^ (n - (i : ℕ)) * Polynomial.aeval (jqModC Qb) (b i) * (ϖc * g) ^ (i : ℕ) = _
        rw [mul_pow, show ϖc ^ n = ϖc ^ (n - (i : ℕ)) * ϖc ^ (i : ℕ) from by
          rw [← pow_add, Nat.sub_add_cancel (le_of_lt i.2)]]
        ring
      have h2 : G ^ n = ϖc ^ n * g ^ n := by rw [hG, mul_pow]
      rw [h2, Finset.sum_congr rfl fun i _ => key i, ← Finset.mul_sum, ← mul_add]
      rw [Finset.sum_range] at heq
      rw [heq, mul_zero]
    refine ⟨Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (C i) * Polynomial.X ^ (i : ℕ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add ((Polynomial.degree_sum_fin_lt C).trans_le le_rfl)
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      exact hGeq
  obtain ⟨r₁, hr₁⟩ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow_mul (R := ↥(R₀ q A red a K)) (FractionRing ↥(R₀ q A red a K)) cϖ hcϖ0 hprime f hv hintR
  have hgR : g ∈ R₀ q A red a K := by
    have : (r₁ : LQ) = g := by rw [← hφf, ← hr₁]; exact (hφalg r₁).symm
    rw [← this]; exact r₁.2

  obtain ⟨r', s', hs', e⟩ := hgR
  refine ⟨MvPolynomial.map (incl A K) r', MvPolynomial.map (incl A K) s', ?_, ?_⟩
  · rw [pointEval_map_incl]; exact hs'
  · rw [modularEval_map_incl, modularEval_map_incl]; exact e

end Main
end RegG
end ModularCurve

open ModularCurve.RegG in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ a : A, red a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ)}) g)
    (x₀ : A) (hb : red x₀ ^ (q ^ 2) ≠ red x₀) :
    g ∈ modularLocalizedAtPoint (1 * q) A.toSubring red (red x₀) (red x₀ ^ q) :=
  ModularCurve.RegG.mainRegG red hker g hg hint x₀ hb

end

end S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral (solution)
