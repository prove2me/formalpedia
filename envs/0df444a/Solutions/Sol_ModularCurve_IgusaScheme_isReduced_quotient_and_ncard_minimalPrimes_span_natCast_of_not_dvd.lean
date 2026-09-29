-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/feb19209-df97-55ac-8292-2726122906c7

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_atkinLehnerInvolutionFull
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
open IntermediateField ModularCurve ModularCurve.IgusaScheme Polynomial

namespace IgusaSpecialFibreTwoBranches

section ValuationHelpers

variable {K : Type*} [Field K]

theorem isUnit_iff_inv_mem (A : ValuationSubring K) {a : K} (ha : a ∈ A) (ha0 : a ≠ 0) :
    IsUnit (⟨a, ha⟩ : A) ↔ a⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : ((↑u⁻¹ : A) : K) * a = 1 := by
      have := congrArg (fun y : A => (y : K)) u.inv_mul
      simpa [hu] using this
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ ha0),
      Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

theorem mem_nonunits_iff' (A : ValuationSubring K) (a : K) :
    a ∈ A.nonunits ↔ a ∈ A ∧ (a = 0 ∨ a⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨ha, hm⟩
    refine ⟨ha, ?_⟩
    by_cases ha0 : a = 0
    · exact Or.inl ha0
    · right
      intro hinv
      exact ((IsLocalRing.mem_maximalIdeal _).mp hm) ((isUnit_iff_inv_mem A ha ha0).mpr hinv)
  · rintro ⟨ha, h⟩
    refine ⟨ha, (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_⟩
    rcases h with h0 | hinv
    · subst h0
      exact not_isUnit_zero (by
        have : (⟨(0 : K), ha⟩ : A) = 0 := Subtype.ext rfl
        rwa [this] at hu)
    · have ha0 : a ≠ 0 := by
        rintro rfl
        have : (⟨(0 : K), ha⟩ : A) = 0 := Subtype.ext rfl
        rw [this] at hu; exact not_isUnit_zero hu
      exact hinv ((isUnit_iff_inv_mem A ha ha0).mp hu)

theorem mem_of_mem_nonunits (A : ValuationSubring K) {a : K} (h : a ∈ A.nonunits) : a ∈ A :=
  ((mem_nonunits_iff' A a).mp h).1

theorem not_mem_nonunits_of_inv_mem (A : ValuationSubring K) {a : K} (ha0 : a ≠ 0)
    (h : a⁻¹ ∈ A) : a ∉ A.nonunits := fun hn =>
  ((mem_nonunits_iff' A a).mp hn).2.elim ha0 (fun h' => h' h)

theorem mul_mem_nonunits (A : ValuationSubring K) {a b : K} (ha : a ∈ A.nonunits) (hb : b ∈ A) :
    a * b ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at ha ⊢
  rw [map_mul]
  calc A.valuation a * A.valuation b ≤ A.valuation a * 1 :=
        mul_le_mul_right ((A.valuation_le_one_iff b).mpr hb) _
    _ = A.valuation a := mul_one _
    _ < 1 := ha

theorem add_mem_nonunits (A : ValuationSubring K) {a b : K} (ha : a ∈ A.nonunits)
    (hb : b ∈ A.nonunits) : a + b ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at ha hb ⊢
  exact Valuation.map_add_lt _ ha hb

theorem zero_mem_nonunits (A : ValuationSubring K) : (0 : K) ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one

theorem one_not_mem_nonunits (A : ValuationSubring K) : (1 : K) ∉ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_one]; exact lt_irrefl _

theorem mem_nonunits_or_of_mul (A : ValuationSubring K) {a b : K} (ha : a ∈ A) (hb : b ∈ A)
    (h : a * b ∈ A.nonunits) : a ∈ A.nonunits ∨ b ∈ A.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff] at h ⊢
  by_contra hc
  push Not at hc
  have ha1 : A.valuation a = 1 := le_antisymm ((A.valuation_le_one_iff a).mpr ha) hc.1
  have hb1 : A.valuation b = 1 := le_antisymm ((A.valuation_le_one_iff b).mpr hb) hc.2
  rw [map_mul, ha1, hb1, mul_one] at h
  exact lt_irrefl _ h

theorem pow_mem_nonunits (A : ValuationSubring K) {a : K} (ha : a ∈ A.nonunits) {n : ℕ}
    (hn : n ≠ 0) : a ^ n ∈ A.nonunits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ']
  exact mul_mem_nonunits A ha (pow_mem (mem_of_mem_nonunits A ha) m)

theorem mem_nonunits_of_pow_mem_nonunits (A : ValuationSubring K) {a : K} (ha : a ∈ A) {n : ℕ}
    (h : a ^ n ∈ A.nonunits) : a ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at h ⊢
  rw [map_pow] at h
  by_contra h'
  have h1 : A.valuation a = 1 := le_antisymm ((A.valuation_le_one_iff a).mpr ha) (not_lt.mp h')
  rw [h1, one_pow] at h
  exact lt_irrefl _ h

theorem mem_of_isIntegral_of_le (A : ValuationSubring K) {R : Subring K} (hR : R ≤ A.toSubring)
    {x : K} (hx : IsIntegral R x) : x ∈ A := by
  have hx' : IsIntegral A.toSubring x :=
    hx.map_of_comp_eq (Subring.inclusion hR) (RingHom.id K) (by ext; rfl)
  haveI : IsIntegrallyClosedIn A.toSubring K := inferInstanceAs (IsIntegrallyClosedIn A K)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := A.toSubring) (A := K)).mp hx'
  rw [← hy]; exact y.2

end ValuationHelpers

end IgusaSpecialFibreTwoBranches

namespace IgusaSpecialFibreTwoBranches

section Setting

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull (N * p)) : Type)
set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)

scoped instance instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem jFull_eq : (jFull (N * p) : F) =
    ⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩ := rfl

abbrev evZ (z : F) (P : ℤ[X]) : F := P.eval₂ (algebraMap ℤ F) z

abbrev redP (P : ℤ[X]) : (ZMod p)[X] := P.map (Int.castRingHom (ZMod p))

def Generic (z : F) (V : ValuationSubring F) : Prop :=
  ((p : ℕ) : F) ∈ V.nonunits ∧
    ∀ P : ℤ[X], redP p P ≠ 0 → evZ N p z P ∈ V ∧ (evZ N p z P)⁻¹ ∈ V

variable {N p}

theorem Generic.p_mem {z : F} {V : ValuationSubring F} (h : Generic N p z V) :
    ((p : ℕ) : F) ∈ V.nonunits := h.1

theorem Generic.mem {z : F} {V : ValuationSubring F} (h : Generic N p z V) {P : ℤ[X]}
    (hP : redP p P ≠ 0) : evZ N p z P ∈ V := (h.2 P hP).1

theorem Generic.inv_mem {z : F} {V : ValuationSubring F} (h : Generic N p z V) {P : ℤ[X]}
    (hP : redP p P ≠ 0) : (evZ N p z P)⁻¹ ∈ V := (h.2 P hP).2

theorem redP_C_ne_zero {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) : redP p (C b) ≠ 0 := by
  unfold redP
  rw [Polynomial.map_C, Ne, Polynomial.C_eq_zero, eq_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hb

theorem redP_X_ne_zero : redP p (X : ℤ[X]) ≠ 0 := by
  unfold redP
  rw [Polynomial.map_X]; exact Polynomial.X_ne_zero

theorem evZ_C (z : F) (b : ℤ) : evZ N p z (C b) = (b : F) := by
  unfold evZ; rw [eval₂_C, eq_intCast]

theorem evZ_X (z : F) : evZ N p z X = z := by
  unfold evZ; rw [eval₂_X]

theorem Generic.intCast_inv_mem {z : F} {V : ValuationSubring F} (h : Generic N p z V) {b : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) : ((b : F))⁻¹ ∈ V := by
  have := h.inv_mem (redP_C_ne_zero hb)
  rwa [evZ_C] at this

theorem Generic.gen_mem {z : F} {V : ValuationSubring F} (h : Generic N p z V) :
    z ∈ V ∧ z⁻¹ ∈ V := by
  have h1 := h.mem (redP_X_ne_zero (p := p))
  have h2 := h.inv_mem (redP_X_ne_zero (p := p))
  rw [evZ_X] at h1 h2
  exact ⟨h1, h2⟩

theorem Generic.p_inv_not_mem {z : F} {V : ValuationSubring F} (h : Generic N p z V) :
    ((p : ℕ) : F)⁻¹ ∉ V := by
  have hp0 : ((p : ℕ) : F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rcases ((mem_nonunits_iff' V _).mp h.p_mem).2 with h0 | h0
  · exact absurd h0 hp0
  · exact h0

theorem Generic.ratCast_mem_iff {z : F} {V : ValuationSubring F} (h : Generic N p z V) (r : ℚ) :
    algebraMap ℚ F r ∈ V ↔ r ∈ GaloisRep.ratLocalizedAt p := by
  have hp : p.Prime := Fact.out
  have hr : algebraMap ℚ F r = (r.num : F) / (r.den : F) := by
    rw [eq_ratCast, Rat.cast_def]
  constructor
  · intro hmem
    change r.den.Coprime p
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd

    have hnum : ¬ (p : ℤ) ∣ r.num := by
      intro hn
      have hcop : r.num.natAbs.Coprime r.den := r.reduced
      have h1 : p ∣ r.num.natAbs := by
        rcases hn with ⟨c, hc⟩
        exact ⟨c.natAbs, by rw [hc, Int.natAbs_mul, Int.natAbs_natCast]⟩
      have h2 : Nat.Coprime p r.den := Nat.Coprime.coprime_dvd_left h1 hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h2 hdvd)
    have hden0 : (r.den : F) ≠ 0 := by exact_mod_cast r.den_ne_zero
    have h1 : ((r.den : F))⁻¹ ∈ V := by
      have : ((r.den : F))⁻¹ = algebraMap ℚ F r * ((r.num : F))⁻¹ := by
        rw [hr]
        have hnum0 : (r.num : F) ≠ 0 := by
          intro h0
          apply hnum
          have : (r.num : F) = ((r.num : ℤ) : F) := rfl
          have h00 : r.num = 0 := by exact_mod_cast h0
          rw [h00]; exact dvd_zero _
        field_simp
      rw [this]
      exact mul_mem hmem (h.intCast_inv_mem hnum)
    obtain ⟨d, hd⟩ := hdvd
    apply h.p_inv_not_mem
    have : ((p : ℕ) : F)⁻¹ = (d : F) * ((r.den : F))⁻¹ := by
      have hp0 : ((p : ℕ) : F) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hd0 : (d : F) ≠ 0 := by
        intro h0
        have : (d : ℕ) = 0 := by exact_mod_cast h0
        rw [this, mul_zero] at hd; exact r.den_ne_zero hd
      rw [hd]; push_cast; field_simp
    rw [this]
    exact mul_mem (natCast_mem V d) h1
  · intro hmem
    change r.den.Coprime p at hmem
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd] at hmem
    rw [hr, div_eq_mul_inv]
    refine mul_mem (intCast_mem V r.num) ?_
    have := h.intCast_inv_mem (b := (r.den : ℤ)) (by exact_mod_cast hmem)
    simpa using this

theorem Generic.algebraMap_mem {z : F} {V : ValuationSubring F} (h : Generic N p z V) (r : ℤp) :
    algebraMap ℤp F r ∈ V := by
  have : algebraMap ℤp F r = algebraMap ℚ F (r : ℚ) := rfl
  rw [this, h.ratCast_mem_iff]
  exact r.2

theorem Generic.adjoin_le {z : F} {V : ValuationSubring F} (h : Generic N p z V) :
    (Algebra.adjoin ℤp ({z} : Set F)).toSubring ≤ V.toSubring := by
  intro x hx
  change x ∈ Algebra.adjoin ℤp ({z} : Set F) at hx
  change x ∈ V
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h.gen_mem.1
  | algebraMap r => exact h.algebraMap_mem r
  | add _ _ _ _ ha hb => exact add_mem ha hb
  | mul _ _ _ _ ha hb => exact mul_mem ha hb

theorem evZ_eq_aeval (z : F) (P : ℤ[X]) :
    evZ N p z P = aeval z (P.map (algebraMap ℤ ℤp)) := by
  unfold evZ
  rw [aeval_def, eval₂_map]
  congr 1

theorem evZ_mem_adjoin (z : F) (P : ℤ[X]) : evZ N p z P ∈ Algebra.adjoin ℤp ({z} : Set F) := by
  rw [evZ_eq_aeval]
  exact Polynomial.aeval_mem_adjoin_singleton _ _

theorem redP_reverse_ne_zero {P : ℤ[X]} (hP : redP p P ≠ 0) : redP p P.reverse ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, (redP p P).coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Polynomial.ext fun i => by rw [h i, coeff_zero])
  intro h0
  apply hi
  have h1 : (redP p P.reverse).coeff (revAt P.natDegree i) = 0 := by rw [h0, coeff_zero]
  unfold redP at h1 ⊢
  rw [coeff_map, coeff_reverse, revAt_invol] at h1
  rw [coeff_map]
  exact h1

theorem evZ_inv_mem_and_inv_mem {V : ValuationSubring F} {z : F} (hz0 : z ≠ 0) (hz : z ∈ V)
    (hzi : z⁻¹ ∈ V)
    (h : ∀ Q : ℤ[X], redP p Q ≠ 0 → evZ N p z Q ∈ V ∧ (evZ N p z Q)⁻¹ ∈ V)
    (P : ℤ[X]) (hP : redP p P ≠ 0) :
    evZ N p z⁻¹ P ∈ V ∧ (evZ N p z⁻¹ P)⁻¹ ∈ V := by
  letI : Invertible (z⁻¹ : F) := invertibleOfNonzero (inv_ne_zero hz0)
  have hinv : (⅟(z⁻¹ : F)) = z := by rw [invOf_eq_inv, inv_inv]
  have key : evZ N p z⁻¹ P = evZ N p z P.reverse * (z⁻¹) ^ P.natDegree := by
    have := Polynomial.eval₂_reverse_mul_pow (algebraMap ℤ F) (z⁻¹ : F) P
    rw [hinv] at this
    exact this.symm
  obtain ⟨h1, h2⟩ := h P.reverse (redP_reverse_ne_zero hP)
  refine ⟨?_, ?_⟩
  · rw [key]; exact mul_mem h1 (pow_mem hzi _)
  · rw [key, mul_inv, inv_pow, inv_inv]; exact mul_mem h2 (pow_mem hz _)

theorem Generic.inv {z : F} {V : ValuationSubring F} (hz0 : z ≠ 0) (h : Generic N p z V) :
    Generic N p z⁻¹ V :=
  ⟨h.p_mem, evZ_inv_mem_and_inv_mem hz0 h.gen_mem.1 h.gen_mem.2 h.2⟩

theorem generic_inv_iff {z : F} (hz0 : z ≠ 0) (V : ValuationSubring F) :
    Generic N p z⁻¹ V ↔ Generic N p z V := by
  refine ⟨fun h => ?_, fun h => h.inv hz0⟩
  have := h.inv (inv_ne_zero hz0)
  rwa [inv_inv] at this

theorem redP_ne_zero_of_isPrimitive {Q : ℤ[X]} (hQ : Q.IsPrimitive) : redP p Q ≠ 0 := by
  intro h0
  have hdvd : ∀ i, (p : ℤ) ∣ Q.coeff i := fun i => by
    have h1 : (redP p Q).coeff i = 0 := by rw [h0, coeff_zero]
    unfold redP at h1
    rw [coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    exact h1
  have hu : IsUnit (p : ℤ) := hQ _ ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd)
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast h1)
  · have : (0 : ℤ) ≤ p := by exact_mod_cast Nat.zero_le p
    omega

theorem aeval_map_int_eq_evZ (z : F) (Q : ℤ[X]) :
    aeval z (Q.map (algebraMap ℤ ℚ)) = evZ N p z Q := by
  unfold evZ
  rw [aeval_def, eval₂_map]
  congr 1

theorem exists_ratCast_mul_evZ (z : F) (Q : ℚ[X]) :
    ∃ (r : ℚ) (Q₁ : ℤ[X]), redP p Q₁ ≠ 0 ∧ aeval z Q = algebraMap ℚ F r * evZ N p z Q₁ := by
  by_cases hQ : Q = 0
  · refine ⟨0, 1, ?_, by rw [hQ, map_zero, map_zero, zero_mul]⟩
    unfold redP; rw [Polynomial.map_one]; exact one_ne_zero
  obtain ⟨b, hb, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) Q
  set Q₀ : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q with hQ₀
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb

  set d : ℤ := Q₀.content with hd
  set Q₁ : ℤ[X] := Q₀.primPart with hQ₁
  have hdec : Q₀ = C d * Q₁ := Q₀.eq_C_content_mul_primPart
  refine ⟨(d : ℚ) / b, Q₁, redP_ne_zero_of_isPrimitive Q₀.isPrimitive_primPart, ?_⟩
  have h1 : Q₀.map (algebraMap ℤ ℚ) = C (b : ℚ) * Q := by
    rw [hbQ]
    ext i
    simp [Polynomial.coeff_smul]
  have hQ' : Q = C ((b : ℚ)⁻¹) * Q₀.map (algebraMap ℤ ℚ) := by
    rw [h1, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]
  rw [hQ', hdec, Polynomial.map_mul, map_C, map_mul, map_mul, aeval_C, aeval_C,
    aeval_map_int_eq_evZ, ← mul_assoc, ← map_mul, div_eq_inv_mul]
  congr 2

theorem adjoin_le_adjoin_rat (z : F) :
    (Algebra.adjoin ℤp ({z} : Set F) : Set F) ⊆ Algebra.adjoin ℚ ({z} : Set F) := by
  have : Algebra.adjoin ℤp ({z} : Set F) ≤ (Algebra.adjoin ℚ ({z} : Set F)).restrictScalars ℤp :=
    Algebra.adjoin_le (Algebra.subset_adjoin)
  exact this

theorem mem_adjoin_of_mem_adjoin_rat {z : F} {W : ValuationSubring F} (hW : Generic N p z W)
    {x : F} (hx : x ∈ Algebra.adjoin ℚ ({z} : Set F)) (hxW : x ∈ W) :
    x ∈ Algebra.adjoin ℤp ({z} : Set F) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨Q, rfl⟩ := hx
  obtain ⟨r, Q₁, hQ₁, hQ⟩ := exists_ratCast_mul_evZ (N := N) (p := p) z Q
  change aeval z Q ∈ W at hxW
  change aeval z Q ∈ _
  rw [hQ] at hxW ⊢
  by_cases h0 : evZ N p z Q₁ = 0
  · rw [h0, mul_zero]; exact zero_mem _
  have hu := hW.inv_mem hQ₁
  have hr : algebraMap ℚ F r ∈ W := by
    have : algebraMap ℚ F r = algebraMap ℚ F r * evZ N p z Q₁ * (evZ N p z Q₁)⁻¹ := by
      rw [mul_inv_cancel_right₀ h0]
    rw [this]; exact mul_mem hxW hu
  rw [hW.ratCast_mem_iff] at hr
  have : algebraMap ℚ F r = algebraMap ℤp F ⟨r, hr⟩ := rfl
  rw [this]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (evZ_mem_adjoin z Q₁)

theorem exists_eq_p_mul_of_mem_nonunits {z : F} {W : ValuationSubring F} (hW : Generic N p z W)
    (hWp : ∀ f ∈ W.nonunits, f * ((p : ℕ) : F)⁻¹ ∈ W)
    {x : F} (hx : x ∈ Algebra.adjoin ℤp ({z} : Set F)) (hxW : x ∈ W.nonunits) :
    ∃ x' ∈ Algebra.adjoin ℤp ({z} : Set F), x = ((p : ℕ) : F) * x' := by
  have hx' : x ∈ Algebra.adjoin ℚ ({z} : Set F) := adjoin_le_adjoin_rat z hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨Q, rfl⟩ := hx'
  obtain ⟨r, Q₁, hQ₁, hQ⟩ := exists_ratCast_mul_evZ (N := N) (p := p) z Q
  have hp0 : ((p : ℕ) : F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  change aeval z Q ∈ _ at hxW
  change ∃ x' ∈ _, aeval z Q = _
  rw [hQ] at hxW ⊢
  by_cases h0 : evZ N p z Q₁ = 0
  · exact ⟨0, zero_mem _, by rw [h0, mul_zero, mul_zero]⟩
  have hu := hW.inv_mem hQ₁
  have hr : algebraMap ℚ F r ∈ W.nonunits := by
    have : algebraMap ℚ F r = algebraMap ℚ F r * evZ N p z Q₁ * (evZ N p z Q₁)⁻¹ := by
      rw [mul_inv_cancel_right₀ h0]
    rw [this]; exact mul_mem_nonunits W hxW hu
  have hr' : algebraMap ℚ F (r / p) ∈ W := by
    rw [map_div₀, div_eq_mul_inv, map_natCast]
    exact hWp _ hr
  rw [hW.ratCast_mem_iff] at hr'
  refine ⟨algebraMap ℤp F ⟨r / p, hr'⟩ * evZ N p z Q₁,
    mul_mem (Subalgebra.algebraMap_mem _ _) (evZ_mem_adjoin z Q₁), ?_⟩
  have : algebraMap ℤp F ⟨r / p, hr'⟩ = algebraMap ℚ F (r / p) := rfl
  rw [this, ← mul_assoc, map_div₀, map_natCast, mul_div_cancel₀ _ hp0]

theorem exists_valuationSubring_centre {K : Type*} [Field K] (A : Subring K) (Q : Ideal A)
    [Q.IsPrime] : ∃ V : ValuationSubring K, A ≤ V.toSubring ∧ ∀ x : A, x ∈ Q ↔ (x : K) ∈ V.nonunits := by
  set L := LocalSubring.ofPrime A Q with hL
  obtain ⟨V, hle⟩ := L.exists_le_valuationSubring
  obtain ⟨hsub, hloc⟩ := hle
  have hAL : A ≤ L.toSubring := LocalSubring.le_ofPrime A Q
  refine ⟨V, hAL.trans hsub, fun x => ?_⟩

  set a : L.toSubring := algebraMap A L.toSubring x with ha
  have hunit : IsUnit a ↔ x ∉ Q := by
    have h1 : a = LocalSubring.ofPrimeEquiv A Q (algebraMap A (Localization.AtPrime Q) x) :=
      ((LocalSubring.ofPrimeEquiv A Q).commutes x).symm
    rw [h1]
    constructor
    · intro hu
      have := hu.map (LocalSubring.ofPrimeEquiv A Q).symm
      rw [AlgEquiv.symm_apply_apply] at this
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q x).mp this
    · intro hx
      exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q x).mpr hx).map _
  have hxa : (a : K) = x := rfl
  have hxV : (x : K) ∈ V := hsub a.2
  constructor
  · intro hxQ
    rw [mem_nonunits_iff']
    refine ⟨hxV, ?_⟩
    by_cases hx0 : (x : K) = 0
    · exact Or.inl hx0
    · right
      intro hinv
      have hu : IsUnit (Subring.inclusion hsub a) := by
        have : IsUnit (⟨(x : K), hxV⟩ : V) := (isUnit_iff_inv_mem V hxV hx0).mpr hinv
        exact this
      exact (hunit.mp (isUnit_of_map_unit (Subring.inclusion hsub) a hu)) hxQ
  · intro hxn
    by_contra hxQ
    have hu : IsUnit (Subring.inclusion hsub a) := (hunit.mpr hxQ).map _
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      apply hxQ
      have : x = 0 := Subtype.ext h0
      rw [this]; exact Q.zero_mem
    have hu' : IsUnit (⟨(x : K), hxV⟩ : V) := hu
    exact not_mem_nonunits_of_inv_mem V hx0 ((isUnit_iff_inv_mem V hxV hx0).mp hu') hxn

variable (N p)

structure BranchPair (y : F) where
  W : Fin 2 → ValuationSubring F
  generic : ∀ i, Generic N p y (W i)
  unif : ∀ i, ∀ f ∈ (W i).nonunits, f * ((p : ℕ) : F)⁻¹ ∈ W i
  complete : ∀ V : ValuationSubring F, Generic N p y V → V = W 0 ∨ V = W 1

variable {N p}

section Engine

variable {y : ↥(modularFunctionFieldFull (N * p))} (D : BranchPair N p y)

set_option quotPrecheck false in
local notation "𝒪" => chartAlg (N * p) p ({y} : Set F)
set_option quotPrecheck false in
local notation "Rz" => Algebra.adjoin ℤp ({y} : Set F)

theorem chartAlg_le_of_generic {V : ValuationSubring F} (hV : Generic N p y V) {x : F} (hx : x ∈ 𝒪) :
    x ∈ V :=
  mem_of_isIntegral_of_le V hV.adjoin_le ((mem_chartAlg_iff (N * p) p).mp hx)

theorem coe_natCast_chartAlg : (((p : ℕ) : 𝒪) : F) = ((p : ℕ) : F) := by simp

def centre (i : Fin 2) : Ideal 𝒪 where
  carrier := {x | (x : F) ∈ (D.W i).nonunits}
  add_mem' {a b} ha hb := by
    show ((a + b : 𝒪) : F) ∈ (D.W i).nonunits
    rw [Subalgebra.coe_add]; exact add_mem_nonunits _ ha hb
  zero_mem' := by
    show ((0 : 𝒪) : F) ∈ (D.W i).nonunits
    rw [Subalgebra.coe_zero]; exact zero_mem_nonunits _
  smul_mem' c {x} hx := by
    show ((c • x : 𝒪) : F) ∈ (D.W i).nonunits
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_comm (c : F) (x : F)]
    exact mul_mem_nonunits _ hx (chartAlg_le_of_generic (D.generic i) c.2)

theorem mem_centre_iff (i : Fin 2) (x : 𝒪) : x ∈ centre D i ↔ (x : F) ∈ (D.W i).nonunits := Iff.rfl

scoped instance centre_isPrime (i : Fin 2) : (centre D i).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h1
    have h1' : ((1 : 𝒪) : F) ∈ (D.W i).nonunits := h1
    rw [Subalgebra.coe_one] at h1'
    exact one_not_mem_nonunits _ h1'
  · intro a b hab
    have hab' : ((a * b : 𝒪) : F) ∈ (D.W i).nonunits := hab
    clear hab
    have hab : (a : F) * (b : F) ∈ (D.W i).nonunits := by rwa [Subalgebra.coe_mul] at hab'
    exact mem_nonunits_or_of_mul _ (chartAlg_le_of_generic (D.generic i) a.2)
      (chartAlg_le_of_generic (D.generic i) b.2) hab

theorem natCast_mem_centre (i : Fin 2) : ((p : ℕ) : 𝒪) ∈ centre D i := by
  rw [mem_centre_iff, coe_natCast_chartAlg]; exact (D.generic i).p_mem

theorem span_le_centre (i : Fin 2) : Ideal.span {((p : ℕ) : 𝒪)} ≤ centre D i := by
  rw [Ideal.span_le, Set.singleton_subset_iff]; exact natCast_mem_centre D i

variable (hy : Transcendental ℚ y)
include hy

theorem transcendental_int : Transcendental ℤp y :=
  hy.restrictScalars (R := ℤp) (S := ℚ) Subtype.val_injective

theorem evZ_ne_zero {Q₀ : ℤ[X]} (hQ₀ : redP p Q₀ ≠ 0) : evZ N p y Q₀ ≠ 0 := by
  intro h0
  have hQ0 : Q₀ ≠ 0 := by rintro rfl; exact hQ₀ (by unfold redP; rw [Polynomial.map_zero])
  apply hy
  refine ⟨Q₀.map (algebraMap ℤ ℚ), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (algebraMap ℤ ℚ).injective_int).mpr hQ0
  · rw [aeval_map_int_eq_evZ (N := N) (p := p)]; exact h0

theorem isIntegrallyClosed_adjoin : IsIntegrallyClosed Rz := by
  haveI : IsDiscreteValuationRing ℤp := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsIntegrallyClosed ℤp := inferInstance
  have hinj : Function.Injective (aeval y : ℤp[X] →ₐ[ℤp] F) :=
    transcendental_iff_injective.mp (transcendental_int hy)
  let e : ℤp[X] ≃ₐ[ℤp] Rz :=
    (AlgEquiv.ofInjective (aeval y) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval ℤp y).symm)
  exact IsIntegrallyClosed.of_equiv e.toRingEquiv

omit hy in

def inclRO : (↥(Rz) : Type) →+* (↥(𝒪) : Type) :=
  (Subalgebra.inclusion (adjoin_le_chartAlg (N * p) p ({y} : Set F))).toRingHom

omit hy in

@[reducible] def algRO : Algebra (↥(Rz) : Type) (↥(𝒪) : Type) := (inclRO (y := y)).toAlgebra

attribute [local instance] algRO

omit hy in
theorem coe_algebraMap_RO (r : Rz) : ((algebraMap (↥(Rz) : Type) (↥(𝒪) : Type) r : 𝒪) : F) = (r : F) :=
  rfl

omit hy in
theorem towerRO : IsScalarTower (↥(Rz) : Type) (↥(𝒪) : Type) F :=
  IsScalarTower.of_algebraMap_eq (R := (↥(Rz) : Type)) (S := (↥(𝒪) : Type)) (A := F) (fun _ => rfl)

attribute [local instance] towerRO

omit hy in
theorem isIntegralRO : Algebra.IsIntegral (↥(Rz) : Type) (↥(𝒪) : Type) :=
  ⟨fun x => (isIntegral_algHom_iff (IsScalarTower.toAlgHom (↥(Rz) : Type) (↥(𝒪) : Type) F)
    Subtype.val_injective).mp ((mem_chartAlg_iff (N * p) p).mp x.2)⟩

omit hy in
theorem faithfulRO : FaithfulSMul (↥(Rz) : Type) (↥(𝒪) : Type) :=
  (faithfulSMul_iff_algebraMap_injective (↥(Rz) : Type) (↥(𝒪) : Type)).mpr
    (Subalgebra.inclusion_injective _)

theorem hasGoingDownRO : Algebra.HasGoingDown (↥(Rz) : Type) (↥(𝒪) : Type) := by
  haveI := isIntegralRO (N := N) (p := p) (y := y)
  haveI := faithfulRO (N := N) (p := p) (y := y)
  haveI : IsIntegrallyClosed Rz := isIntegrallyClosed_adjoin hy
  infer_instance

omit hy in

def inclZQ : (↥(Rz) : Type) →+* (↥(Algebra.adjoin ℚ ({y} : Set F)) : Type) where
  toFun x := ⟨x, adjoin_le_adjoin_rat y x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit hy in
theorem adjoin_int_le_Ky : (Rz : Set F) ⊆ (IntermediateField.adjoin ℚ ({y} : Set F) : Set F) :=
  fun _ hx => algebra_adjoin_le_adjoin ℚ _ (adjoin_le_adjoin_rat y hx)

include D in
open scoped IntermediateField.algebraAdjoinAdjoin in

theorem mem_chartAlg_of_p_mul_mem {g : F} (hg : ((p : ℕ) : F) * g ∈ 𝒪)
    (hgV : ∀ V : ValuationSubring F, Generic N p y V → g ∈ V) : g ∈ 𝒪 := by
  have hp0 : ((p : ℕ) : F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  let Ky : IntermediateField ℚ F := IntermediateField.adjoin ℚ ({y} : Set F)
  let A₂ : ValuationSubring Ky := (D.W 0).comap (algebraMap Ky F)
  letI algA₂ : Algebra A₂ F := ((algebraMap Ky F).comp (algebraMap A₂ Ky)).toAlgebra
  haveI towA₂ : IsScalarTower A₂ Ky F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsIntegrallyClosed (Algebra.adjoin ℚ ({y} : Set F)) :=
    Subalgebra.isIntegrallyClosed_adjoin_singleton_of_transcendental y hy

  have hf : IsIntegral Rz (((p : ℕ) : F) * g) := (mem_chartAlg_iff (N * p) p).mp hg
  have hf₁ : IsIntegral (Algebra.adjoin ℚ ({y} : Set F)) (((p : ℕ) : F) * g) :=
    hf.map_of_comp_eq (inclZQ (y := y)) (RingHom.id F) (by ext; rfl)
  have hint₁ : IsIntegral (Algebra.adjoin ℚ ({y} : Set F)) g := by
    have hpinv : IsIntegral (Algebra.adjoin ℚ ({y} : Set F)) (((p : ℕ) : F)⁻¹) := by
      have : ((p : ℕ) : F)⁻¹ = algebraMap (Algebra.adjoin ℚ ({y} : Set F)) F
          ⟨algebraMap ℚ F ((p : ℚ)⁻¹), Subalgebra.algebraMap_mem _ _⟩ := by
        show _ = algebraMap ℚ F ((p : ℚ)⁻¹)
        rw [map_inv₀, map_natCast]
      rw [this]; exact isIntegral_algebraMap
    have := hpinv.mul hf₁
    rwa [inv_mul_cancel_left₀ hp0] at this

  have hKW : ∀ (V : ValuationSubring F), (integralClosure A₂ F).toSubring ≤ V.toSubring →
      ∀ c : Ky, (c : F) ∈ D.W 0 → (c : F) ∈ V := fun V hV c hc =>
    hV (show (c : F) ∈ (integralClosure A₂ F).toSubring from
      (integralClosure A₂ F).algebraMap_mem ⟨c, hc⟩)
  have hint₂ : IsIntegral A₂ g := by
    by_contra hnot
    have hg' : g ∉ (integralClosure A₂ F).toSubring := fun h => hnot h
    obtain ⟨V, hV, hgV'⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hg'
    apply hgV'
    by_cases hpV : ((p : ℕ) : F)⁻¹ ∈ V
    ·
      have hRV : (Rz).toSubring ≤ V.toSubring := by
        intro x hx
        change x ∈ Rz at hx
        change x ∈ V
        induction hx using Algebra.adjoin_induction with
        | mem z hz =>
          rw [Set.mem_singleton_iff.mp hz]
          exact hKW V hV ⟨y, mem_adjoin_simple_self ℚ y⟩ (D.generic 0).gen_mem.1
        | algebraMap r =>
          exact hKW V hV ⟨algebraMap ℤp F r, Ky.algebraMap_mem (r : ℚ)⟩ ((D.generic 0).algebraMap_mem r)
        | add _ _ _ _ ha hb => exact add_mem ha hb
        | mul _ _ _ _ ha hb => exact mul_mem ha hb
      have hfV : ((p : ℕ) : F) * g ∈ V := mem_of_isIntegral_of_le V hRV hf
      have : g = ((p : ℕ) : F)⁻¹ * (((p : ℕ) : F) * g) := by rw [inv_mul_cancel_left₀ hp0]
      rw [this]; exact mul_mem hpV hfV
    · apply hgV V
      refine ⟨(mem_nonunits_iff' V _).mpr ⟨natCast_mem V p, Or.inr hpV⟩, fun Q₀ hQ₀ => ⟨?_, ?_⟩⟩
      · exact hKW V hV ⟨evZ N p y Q₀, adjoin_int_le_Ky (evZ_mem_adjoin y Q₀)⟩ ((D.generic 0).mem hQ₀)
      · exact hKW V hV ⟨(evZ N p y Q₀)⁻¹, inv_mem (adjoin_int_le_Ky (evZ_mem_adjoin y Q₀))⟩
          ((D.generic 0).inv_mem hQ₀)

  have hK : IsIntegral Ky g := hint₁.tower_top
  have e₁ := minpoly.isIntegrallyClosed_eq_field_fractions' (K := (Ky : Type)) hint₁
  have e₂ := minpoly.isIntegrallyClosed_eq_field_fractions' (K := (Ky : Type)) hint₂
  have hcoef : ∀ i, (((minpoly Ky g).coeff i : Ky) : F) ∈ Rz := fun i => by
    apply mem_adjoin_of_mem_adjoin_rat (D.generic 0)
    · rw [e₁, coeff_map]
      exact ((minpoly (Algebra.adjoin ℚ ({y} : Set F)) g).coeff i).2
    · rw [e₂, coeff_map]
      exact ((minpoly A₂ g).coeff i).2

  have hmonic : (minpoly Ky g).Monic := minpoly.monic hK
  have hlifts : (minpoly Ky g).map (algebraMap Ky F) ∈ Polynomial.lifts (algebraMap Rz F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, hcoef i⟩, rfl⟩
  obtain ⟨P, hPmap, -, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hmonic.map _)
  refine (mem_chartAlg_iff (N * p) p).mpr ⟨P, hPmonic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hPmap, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]

include D in

theorem isRadical_span : (Ideal.span {((p : ℕ) : 𝒪)}).IsRadical := by
  have hp0 : ((p : ℕ) : F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  intro f hf
  obtain ⟨n, hn⟩ := hf
  by_cases hn0 : n = 0
  · subst hn0
    rw [pow_zero] at hn
    have : Ideal.span {((p : ℕ) : 𝒪)} = ⊤ := (Ideal.eq_top_iff_one _).mpr hn
    rw [this]; trivial
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn
  set g : F := ((p : ℕ) : F)⁻¹ * (f : F) with hgdef
  have hg : ((p : ℕ) : F) * g = f := by rw [hgdef, mul_inv_cancel_left₀ hp0]
  have hg𝒪 : ((p : ℕ) : F) * g ∈ 𝒪 := by rw [hg]; exact f.2
  have hgV : ∀ V : ValuationSubring F, Generic N p y V → g ∈ V := by
    have key : ∀ i, g ∈ D.W i := fun i => by
      have hfW : (f : F) ∈ D.W i := chartAlg_le_of_generic (D.generic i) f.2
      have hcW : (c : F) ∈ D.W i := chartAlg_le_of_generic (D.generic i) c.2
      have hfn : (f : F) ^ n ∈ (D.W i).nonunits := by
        have : (f : F) ^ n = ((p : ℕ) : F) * (c : F) := by
          rw [← Subalgebra.coe_pow, ← hc, Subalgebra.coe_mul, coe_natCast_chartAlg]; exact mul_comm _ _
        rw [this]; exact mul_mem_nonunits _ (D.generic i).p_mem hcW
      have hfnu : (f : F) ∈ (D.W i).nonunits := mem_nonunits_of_pow_mem_nonunits _ hfW hfn
      have := D.unif i _ hfnu
      rwa [mul_comm (f : F) _] at this
    intro V hV
    rcases D.complete V hV with rfl | rfl <;> exact key _
  have hgO := mem_chartAlg_of_p_mul_mem D hy hg𝒪 hgV
  refine Ideal.mem_span_singleton'.mpr ⟨⟨g, hgO⟩, Subtype.ext ?_⟩
  rw [Subalgebra.coe_mul, coe_natCast_chartAlg]; exact (mul_comm _ _).trans hg

include D in

theorem evZ_not_mem_of_isMinimalPrime {Q : Ideal 𝒪}
    (hQ : Q ∈ (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes) {Q₀ : ℤ[X]} (hQ₀ : redP p Q₀ ≠ 0) :
    (⟨evZ N p y Q₀, adjoin_le_chartAlg (N * p) p _ (evZ_mem_adjoin y Q₀)⟩ : 𝒪) ∉ Q := by
  intro hmem
  haveI : Q.IsPrime := hQ.1.1
  haveI : Algebra.HasGoingDown (↥(Rz) : Type) (↥(𝒪) : Type) := hasGoingDownRO hy
  have hpQ : ((p : ℕ) : 𝒪) ∈ Q := hQ.1.2 (Ideal.subset_span rfl)

  set 𝔮 : Ideal Rz := Q.under Rz with h𝔮
  set 𝔮' : Ideal Rz := (centre D 0).under Rz with h𝔮'
  have hle : 𝔮' ≤ 𝔮 := by
    intro r hr
    rw [h𝔮', Ideal.mem_comap] at hr
    change ((r : F)) ∈ (D.W 0).nonunits at hr
    obtain ⟨x', hx', hx⟩ := exists_eq_p_mul_of_mem_nonunits (D.generic 0) (D.unif 0) r.2 hr
    rw [h𝔮, Ideal.mem_comap]
    have : algebraMap Rz 𝒪 r = ((p : ℕ) : 𝒪) * ⟨x', adjoin_le_chartAlg (N * p) p _ hx'⟩ :=
      Subtype.ext (by rw [Subalgebra.coe_mul, coe_natCast_chartAlg, ← hx]; rfl)
    rw [this]
    exact Q.mul_mem_right _ hpQ
  set r₀ : Rz := ⟨evZ N p y Q₀, evZ_mem_adjoin y Q₀⟩ with hr₀
  have hr₀𝔮 : r₀ ∈ 𝔮 := by rw [h𝔮, Ideal.mem_comap]; exact hmem
  have hr₀𝔮' : r₀ ∉ 𝔮' := by
    rw [h𝔮', Ideal.mem_comap]
    change ¬ ((evZ N p y Q₀ : F) ∈ (D.W 0).nonunits)
    exact not_mem_nonunits_of_inv_mem _ (evZ_ne_zero hy hQ₀) ((D.generic 0).inv_mem hQ₀)
  have hlt : 𝔮' < 𝔮 := lt_of_le_of_ne hle (fun h => hr₀𝔮' (h ▸ hr₀𝔮))
  obtain ⟨P', hP'lt, hP'prime, hP'over⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (p := 𝔮') (q := 𝔮) Q hlt

  have hpP' : ((p : ℕ) : 𝒪) ∈ P' := by
    have h1 : ((p : ℕ) : Rz) ∈ 𝔮' := by
      rw [h𝔮', Ideal.mem_comap, map_natCast]; exact natCast_mem_centre D 0
    have h2 := (P'.mem_of_liesOver 𝔮' ((p : ℕ) : Rz)).mp h1
    rwa [map_natCast] at h2
  have hspan : Ideal.span {((p : ℕ) : 𝒪)} ≤ P' := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hpP'
  exact (lt_irrefl Q) (lt_of_le_of_lt (hQ.2 ⟨hP'prime, hspan⟩ hP'lt.le) hP'lt)

theorem eq_centre_of_isMinimalPrime {Q : Ideal 𝒪}
    (hQ : Q ∈ (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes) : Q = centre D 0 ∨ Q = centre D 1 := by
  haveI : Q.IsPrime := hQ.1.1
  obtain ⟨V, hOV, hQV⟩ := exists_valuationSubring_centre (chartAlg (N * p) p ({y} : Set F)).toSubring Q
  have hpQ : ((p : ℕ) : 𝒪) ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
  have hgen : Generic N p y V := by
    refine ⟨?_, fun Q₀ hQ₀ => ?_⟩
    · have := (hQV _).mp hpQ
      rwa [coe_natCast_chartAlg] at this
    · set e : 𝒪 := ⟨evZ N p y Q₀, adjoin_le_chartAlg (N * p) p _ (evZ_mem_adjoin y Q₀)⟩ with he
      have heV : (e : F) ∈ V := hOV e.2
      have hnot : (e : F) ∉ V.nonunits := fun h => evZ_not_mem_of_isMinimalPrime D hy hQ hQ₀ ((hQV e).mpr h)
      refine ⟨heV, ?_⟩
      rw [mem_nonunits_iff'] at hnot
      push Not at hnot
      exact (hnot heV).2
  rcases D.complete V hgen with hV | hV
  · left
    ext x
    rw [hQV x, mem_centre_iff, hV]
  · right
    ext x
    rw [hQV x, mem_centre_iff, hV]

theorem minimalPrimes_eq
    (ht : ∃ t ∈ 𝒪, t ∈ (D.W 0).nonunits ∧ t ∉ (D.W 1).nonunits)
    (ht' : ∃ t' ∈ 𝒪, t' ∈ (D.W 1).nonunits ∧ t' ∉ (D.W 0).nonunits) :
    (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes = {centre D 0, centre D 1} := by
  obtain ⟨t, ht𝒪, ht0, ht1⟩ := ht
  obtain ⟨t', ht'𝒪, ht'1, ht'0⟩ := ht'
  have h01 : ¬ centre D 0 ≤ centre D 1 := fun h => ht1 (h (show (⟨t, ht𝒪⟩ : 𝒪) ∈ centre D 0 from ht0))
  have h10 : ¬ centre D 1 ≤ centre D 0 := fun h => ht'0 (h (show (⟨t', ht'𝒪⟩ : 𝒪) ∈ centre D 1 from ht'1))
  have hmin0 : centre D 0 ∈ (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes := by
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (span_le_centre D 0)
    rcases eq_centre_of_isMinimalPrime D hy hQ with rfl | rfl
    · exact hQ
    · exact absurd hQle h10
  have hmin1 : centre D 1 ∈ (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes := by
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (span_le_centre D 1)
    rcases eq_centre_of_isMinimalPrime D hy hQ with rfl | rfl
    · exact absurd hQle h01
    · exact hQ
  ext Q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨fun hQ => eq_centre_of_isMinimalPrime D hy hQ, ?_⟩
  rintro (rfl | rfl)
  · exact hmin0
  · exact hmin1

theorem ncard_minimalPrimes
    (ht : ∃ t ∈ 𝒪, t ∈ (D.W 0).nonunits ∧ t ∉ (D.W 1).nonunits)
    (ht' : ∃ t' ∈ 𝒪, t' ∈ (D.W 1).nonunits ∧ t' ∉ (D.W 0).nonunits) :
    (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes.ncard = 2 := by
  rw [minimalPrimes_eq D hy ht ht']
  apply Set.ncard_pair
  intro h
  obtain ⟨t, ht𝒪, ht0, ht1⟩ := ht
  exact ht1 ((mem_centre_iff D 1 ⟨t, ht𝒪⟩).mp (h ▸ (show (⟨t, ht𝒪⟩ : 𝒪) ∈ centre D 0 from ht0)))

end Engine

section Instantiate

variable (N p)

set_option quotPrecheck false in
local notation "jF" => (jFull (N * p) : F)
set_option quotPrecheck false in
local notation "w" => atkinLehnerInvolutionFull N p

abbrev ιQ : LaurentSeries ℤ →+* LaurentSeries ℚ := coeffMap (Int.castRingHom ℚ)
abbrev ϖ : LaurentSeries ℤ →+* LaurentSeries (ZMod p) := coeffMap (Int.castRingHom (ZMod p))

theorem ιQ_injective : Function.Injective ιQ := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries ℚ => s.coeff n) h
  simp only [coeffMap_coeff, eq_intCast, Int.cast_inj] at h1
  exact h1

theorem transcendental_jFull : Transcendental ℚ jF := by
  rintro ⟨P, hP0, hP⟩
  apply ModularCurve.transcendental_jqModC ℚ
  refine ⟨P, hP0, ?_⟩
  have hg : (algebraMap F (LaurentSeries ℚ)).comp (algebraMap ℚ F) = algebraMap ℚ (LaurentSeries ℚ) :=
    RingHom.ext fun r => (eq_ratCast _ r).trans (eq_ratCast _ r).symm
  have h := congrArg (algebraMap F (LaurentSeries ℚ)) hP
  rw [aeval_def, Polynomial.hom_eval₂, hg, map_zero] at h
  rw [aeval_def]
  exact h

theorem jFull_ne_zero' : jF ≠ 0 := jFull_ne_zero (N * p)

theorem transcendental_jFull_inv : Transcendental ℚ jF⁻¹ := fun h =>
  transcendental_jFull (N := N) (p := p) (IsAlgebraic.inv_iff.mp h)

def jpF : F := ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩

theorem coe_jF : ((jF : F) : LaurentSeries ℚ) = ιQ (jqModC ℤ) := by
  change jq = _; rw [coeffMap_jqModC, jqModC_rat]

theorem coe_jpF : ((jpF N p : F) : LaurentSeries ℚ) = ιQ (qExpand ℤ p (jqModC ℤ)) := by
  change qExpand ℚ p jq = _; rw [coeffMap_qExpand, coeffMap_jqModC, jqModC_rat]

theorem atkinLehner_swap (hpN : ¬ p ∣ N) : w jF = jpF N p ∧ w (jpF N p) = jF := by
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  obtain ⟨h1, h2⟩ := hσ 1 inferInstance (one_dvd N)
  have hjF : (jF : F) = ⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ :=
    Subtype.ext (by change jq = qExpand ℚ 1 jq; rw [qExpand_one_apply])
  have hjpF : jpF N p = ⟨qExpand ℚ (1 * p) jq, jqd_mem_full (N * p) (Nat.mul_dvd_mul_right (one_dvd N) p)⟩ :=
    Subtype.ext (by change qExpand ℚ p jq = qExpand ℚ (1 * p) jq; rw [qExpand_congr (one_mul p)])
  rw [hjF, hjpF]
  exact ⟨h1, h2⟩

def tFun : F := jpF N p - jF ^ p

def tZ : LaurentSeries ℤ := qExpand ℤ p (jqModC ℤ) - (jqModC ℤ) ^ p
def tZ' : LaurentSeries ℤ := jqModC ℤ - (qExpand ℤ p (jqModC ℤ)) ^ p

theorem coe_tFun : ((tFun N p : F) : LaurentSeries ℚ) = ιQ (tZ p) := by
  rw [tFun, tZ, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_jpF, coe_jF, map_sub, map_pow]

theorem w_tFun (hpN : ¬ p ∣ N) : w (tFun N p) = jF - (jpF N p) ^ p := by
  obtain ⟨h1, h2⟩ := atkinLehner_swap N p hpN
  rw [tFun, map_sub, map_pow, h1, h2]

theorem coe_w_tFun (hpN : ¬ p ∣ N) : ((w (tFun N p) : F) : LaurentSeries ℚ) = ιQ (tZ' p) := by
  rw [w_tFun N p hpN, tZ', AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_jpF, coe_jF, map_sub,
    map_pow]

theorem ϖ_tZ : ϖ p (tZ p) = 0 := by
  rw [tZ, map_sub, map_pow, coeffMap_qExpand, coeffMap_jqModC,
    qExpand_jqModC_eq_pow_unconditional (ZMod p), sub_self]

theorem ϖ_tZ'_ne_zero : ϖ p (tZ' p) ≠ 0 := by
  rw [tZ', map_sub, map_pow, coeffMap_qExpand, coeffMap_jqModC,
    qExpand_jqModC_eq_pow_unconditional (ZMod p), ← pow_mul, sub_ne_zero]
  intro e
  have h1 : ((jqModC (ZMod p)) ^ 1).order = ((jqModC (ZMod p)) ^ (p * p)).order := by
    rw [pow_one]; exact congrArg HahnSeries.order e
  have ho : ∀ b : ℕ, ((jqModC (ZMod p)) ^ b).order = -(b : ℤ) := by
    intro b
    have hc : ((jqModC (ZMod p)) ^ b).coeff (-(b : ℤ)) ≠ 0 := by
      rw [coeff_jqModC_pow_self]; exact one_ne_zero
    have hne : (jqModC (ZMod p)) ^ b ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hc
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
    by_contra hlt
    push Not at hlt
    exact (fun h0 => hne (HahnSeries.coeff_order_eq_zero.mp h0)) (coeff_jqModC_pow_of_lt (ZMod p) hlt)
  rw [ho, ho] at h1
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h2 : ((p * p : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by linarith
  have h3 : p * p = 1 := by exact_mod_cast h2
  nlinarith

theorem w_tFun_ne_zero (hpN : ¬ p ∣ N) : w (tFun N p) ≠ 0 := by
  intro h0
  have h1 : ((w (tFun N p) : F) : LaurentSeries ℚ) = 0 := by rw [h0]; rfl
  rw [coe_w_tFun N p hpN] at h1
  exact ϖ_tZ'_ne_zero p (by rw [ιQ_injective (h1.trans (map_zero _).symm), map_zero])

theorem tFun_ne_zero (hpN : ¬ p ∣ N) : tFun N p ≠ 0 := fun h =>
  w_tFun_ne_zero N p hpN (by rw [h, map_zero])

theorem tFun_mem_gauss (W₀ : ValuationSubring F)
    (hW₀ : ∀ f : F, f ∈ W₀ ↔ ∃ x y : LaurentSeries ℤ, ϖ p y ≠ 0 ∧ (f : LaurentSeries ℚ) * ιQ y = ιQ x)
    (hpN : ¬ p ∣ N) :
    tFun N p ∈ W₀.nonunits ∧ (w (tFun N p))⁻¹ ∈ W₀ := by
  have h1 : ϖ p 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  constructor
  · rw [mem_nonunits_iff']
    refine ⟨(hW₀ _).mpr ⟨tZ p, 1, h1, by rw [map_one, mul_one, coe_tFun]⟩, ?_⟩
    by_cases h0 : tFun N p = 0
    · exact Or.inl h0
    · right
      rintro hinv
      obtain ⟨x, y, hy, hxy⟩ := (hW₀ _).mp hinv
      apply hy
      have ht0 : ((tFun N p : F) : LaurentSeries ℚ) ≠ 0 := fun e => h0 (Subtype.ext e)
      have : ιQ y = ιQ (tZ p * x) := by
        rw [map_mul, ← hxy, ← coe_tFun N p, IntermediateField.coe_inv, ← mul_assoc,
          mul_inv_cancel₀ ht0, one_mul]
      rw [ιQ_injective this, map_mul, ϖ_tZ, zero_mul]
  · refine (hW₀ _).mpr ⟨1, tZ' p, ϖ_tZ'_ne_zero p, ?_⟩
    have ht0 : ((w (tFun N p) : F) : LaurentSeries ℚ) ≠ 0 := fun e =>
      w_tFun_ne_zero N p hpN (Subtype.ext e)
    rw [IntermediateField.coe_inv, ← coe_w_tFun N p hpN, inv_mul_cancel₀ ht0, map_one]

theorem tFun_mem_chartAlgFin (hpN : ¬ p ∣ N) :
    tFun N p ∈ chartAlgFin (N * p) p ∧ w (tFun N p) ∈ chartAlgFin (N * p) p := by
  have hj : (jF : F) ∈ chartAlgFin (N * p) p := subset_chartAlg (N * p) p _ rfl
  have hw : ∀ x : F, x ∈ chartAlgFin (N * p) p → w x ∈ chartAlgFin (N * p) p := fun x hx =>
    (mem_chartAlg_iff (N * p) p).mpr
      (ModularCurve.isIntegral_adjoin_jq_atkinLehnerInvolutionFull N p hpN
        (↥(GaloisRep.ratLocalizedAt p)) x ((mem_chartAlg_iff (N * p) p).mp hx))
  have ht : tFun N p ∈ chartAlgFin (N * p) p := by
    rw [tFun, ← (atkinLehner_swap N p hpN).1]
    exact sub_mem (hw _ hj) (pow_mem hj _)
  exact ⟨ht, hw _ ht⟩

theorem witnesses_fin (W₀ W₁ : ValuationSubring F)
    (hW₀ : ∀ f : F, f ∈ W₀ ↔ ∃ x y : LaurentSeries ℤ, ϖ p y ≠ 0 ∧ (f : LaurentSeries ℚ) * ιQ y = ιQ x)
    (hW₁ : ∀ f : F, f ∈ W₁ ↔ w f ∈ W₀) (hpN : ¬ p ∣ N) :
    (∃ t ∈ chartAlgFin (N * p) p, t ∈ W₀.nonunits ∧ t ∉ W₁.nonunits) ∧
    (∃ t' ∈ chartAlgFin (N * p) p, t' ∈ W₁.nonunits ∧ t' ∉ W₀.nonunits) := by
  obtain ⟨htn, hwinv⟩ := tFun_mem_gauss N p W₀ hW₀ hpN
  obtain ⟨htO, hwtO⟩ := tFun_mem_chartAlgFin N p hpN
  have hww : ∀ x : F, w (w x) = x := ModularCurve.atkinLehnerInvolutionFull_apply_apply N p hpN
  have ht0 := tFun_ne_zero N p hpN
  have hwt0 := w_tFun_ne_zero N p hpN
  refine ⟨⟨tFun N p, htO, htn, ?_⟩, ⟨w (tFun N p), hwtO, ?_, ?_⟩⟩
  · refine not_mem_nonunits_of_inv_mem _ ht0 ?_
    rw [hW₁, map_inv₀]; exact hwinv
  · rw [mem_nonunits_iff']
    refine ⟨by rw [hW₁, hww]; exact mem_of_mem_nonunits _ htn, Or.inr ?_⟩
    rw [hW₁, map_inv₀, hww]
    exact ((mem_nonunits_iff' _ _).mp htn).2.resolve_left ht0
  · exact not_mem_nonunits_of_inv_mem _ hwt0 hwinv

theorem witness_inf {A B : ValuationSubring F} (hA : Generic N p jF A) (hB : Generic N p jF B)
    {t : F} (htO : t ∈ chartAlgFin (N * p) p) (htA : t ∈ A.nonunits) (htB : t ∉ B.nonunits) :
    ∃ s ∈ chartAlgInf (N * p) p, s ∈ A.nonunits ∧ s ∉ B.nonunits := by
  have hj0 : (jF : F) ≠ 0 := jFull_ne_zero (N * p)
  have hji0 : (jF : F)⁻¹ ≠ 0 := inv_ne_zero hj0
  have ht' : t ∈ chartAlg (N * p) p (insert (jF⁻¹)⁻¹ ({jF⁻¹} : Set F)) := by
    refine chartAlg_mono (N * p) p ?_ htO
    rw [inv_inv]; exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton (jF⁻¹ : F)) hji0 ht'
  have htBmem : t ∈ B := by
    have := hB.adjoin_le
    exact chartAlg_le_of_generic hB htO
  have ht0 : t ≠ 0 := fun h => htB (h ▸ zero_mem_nonunits B)
  have htBinv : t⁻¹ ∈ B := by
    have h := (mem_nonunits_iff' B t).not.mp htB
    push Not at h
    exact (h htBmem).2
  refine ⟨(jF⁻¹) ^ n * t, hn, ?_, ?_⟩
  · rw [mul_comm _ t]; exact mul_mem_nonunits _ htA (pow_mem hA.gen_mem.2 _)
  · refine not_mem_nonunits_of_inv_mem _ (mul_ne_zero (pow_ne_zero _ hji0) ht0) ?_
    rw [mul_inv, inv_pow, inv_inv]
    exact mul_mem (pow_mem hB.gen_mem.1 _) htBinv

end Instantiate

end Setting

theorem main (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    IsReduced (↥(chartAlgFin (N * p) p) ⧸ Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}) ∧
    (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes.ncard = 2 ∧
    IsReduced (↥(chartAlgInf (N * p) p) ⧸ Ideal.span {((p : ℕ) : ↥(chartAlgInf (N * p) p))}) ∧
    (Ideal.span {((p : ℕ) : ↥(chartAlgInf (N * p) p))}).minimalPrimes.ncard = 2 := by
  obtain ⟨W, hW1, hW2, -, hW4, hW5⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N p hpN
  have hj0 : (jFull (N * p) : ↥(modularFunctionFieldFull (N * p))) ≠ 0 := jFull_ne_zero (N * p)

  have hgen : ∀ i, Generic N p (jFull (N * p)) (W i) := fun i => ⟨(hW4 i).1, (hW4 i).2.1⟩
  let D : BranchPair N p (jFull (N * p)) :=
    ⟨W, hgen, fun i => (hW4 i).2.2, fun V hV => hW5 V hV.1 hV.2⟩

  let D' : BranchPair N p (jFull (N * p))⁻¹ :=
    ⟨W, fun i => (hgen i).inv hj0, fun i => (hW4 i).2.2,
      fun V hV => hW5 V hV.1 ((generic_inv_iff hj0 V).mp hV).2⟩
  have hyF := transcendental_jFull N p
  have hyI := transcendental_jFull_inv N p
  obtain ⟨⟨t, htO, ht0, ht1⟩, ⟨t', ht'O, ht'1, ht'0⟩⟩ := witnesses_fin N p (W 0) (W 1) hW1 hW2 hpN
  obtain ⟨s, hsO, hs0, hs1⟩ := witness_inf N p (hgen 0) (hgen 1) htO ht0 ht1
  obtain ⟨s', hs'O, hs'1, hs'0⟩ := witness_inf N p (hgen 1) (hgen 0) ht'O ht'1 ht'0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_span D hyF)
  · exact ncard_minimalPrimes D hyF ⟨t, htO, ht0, ht1⟩ ⟨t', ht'O, ht'1, ht'0⟩
  · exact (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_span D' hyI)
  · exact ncard_minimalPrimes D' hyI ⟨s, hsO, hs0, hs1⟩ ⟨s', hs'O, hs'1, hs'0⟩

end IgusaSpecialFibreTwoBranches
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd.IgusaSpecialFibreTwoBranches"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd.IgusaSpecialFibreTwoBranches"

open ModularCurve ModularCurve.IgusaScheme in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    IsReduced (↥(chartAlgFin (N * p) p) ⧸ Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}) ∧
    (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes.ncard = 2 ∧
    IsReduced (↥(chartAlgInf (N * p) p) ⧸ Ideal.span {((p : ℕ) : ↥(chartAlgInf (N * p) p))}) ∧
    (Ideal.span {((p : ℕ) : ↥(chartAlgInf (N * p) p))}).minimalPrimes.ncard = 2 :=
  IgusaSpecialFibreTwoBranches.main N p hpN

end S_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd (solution)
