-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/dfef2636-2a94-5938-a9a3-ec3a7c0a5464

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast
import Theorems.Thm_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
open IntermediateField ModularCurve ModularCurve.IgusaScheme Polynomial

namespace IgusaBranchQExp

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

end IgusaBranchQExp

namespace IgusaBranchQExp

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
  complete : ∀ V : ValuationSubring F, Generic N p y V → V = W 0 ∨ V = W 1

variable {N p}

section Engine

variable {y : ↥(modularFunctionFieldFull (N * p))} (D : BranchPair N p y)

set_option quotPrecheck false in
local notation "𝒪" => chartAlg (N * p) p ({y} : Set F)

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

theorem coe_aeval (Q₀ : ℤ[X]) :
    ((Polynomial.aeval (⟨y, subset_chartAlg (N * p) p _ (Set.mem_singleton y)⟩ : 𝒪) Q₀ : 𝒪) : F) =
      evZ N p y Q₀ := by
  have := Polynomial.aeval_algHom_apply
    ((chartAlg (N * p) p ({y} : Set F)).val.toRingHom.toIntAlgHom)
    (⟨y, subset_chartAlg (N * p) p _ (Set.mem_singleton y)⟩ : 𝒪) Q₀
  exact this.symm

variable (hy : Transcendental ℚ y)
include hy

theorem evZ_ne_zero {Q₀ : ℤ[X]} (hQ₀ : redP p Q₀ ≠ 0) : evZ N p y Q₀ ≠ 0 := by
  intro h0
  have hQ0 : Q₀ ≠ 0 := by rintro rfl; exact hQ₀ (by unfold redP; rw [Polynomial.map_zero])
  apply hy
  refine ⟨Q₀.map (algebraMap ℤ ℚ), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (algebraMap ℤ ℚ).injective_int).mpr hQ0
  · rw [aeval_map_algebraMap]
    unfold evZ at h0
    rw [aeval_def]
    convert h0 using 2

theorem evZ_not_mem_nonunits_of_isMinimalPrime {Q : Ideal 𝒪}
    (hQ : Q ∈ (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes) {V : ValuationSubring F}
    (hQV : ∀ x : 𝒪, x ∈ Q ↔ (x : F) ∈ V.nonunits) {Q₀ : ℤ[X]} (hQ₀ : redP p Q₀ ≠ 0) :
    evZ N p y Q₀ ∉ V.nonunits := by
  intro hmem
  have h := aeval_notMem_of_mem_minimalPrimes_span_natCast (N * p) p y hy Q hQ Q₀ hQ₀
  apply h
  rw [hQV, coe_aeval]
  exact hmem

include D in

theorem eq_centre_of_isMinimalPrime {Q : Ideal 𝒪}
    (hQ : Q ∈ (Ideal.span {((p : ℕ) : 𝒪)}).minimalPrimes) : Q = centre D 0 ∨ Q = centre D 1 := by
  haveI : Q.IsPrime := hQ.1.1
  obtain ⟨V, hOV, hQV⟩ := exists_valuationSubring_centre (chartAlg (N * p) p ({y} : Set F)).toSubring Q
  have hpQ : ((p : ℕ) : 𝒪) ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
  have hgen : Generic N p y V := by
    refine ⟨?_, fun Q₀ hQ₀ => ?_⟩
    · have := (hQV _).mp hpQ
      rwa [coe_natCast_chartAlg] at this
    · have heV : evZ N p y Q₀ ∈ V :=
        hOV (adjoin_le_chartAlg (N * p) p _ (evZ_mem_adjoin y Q₀))
      have hnot : evZ N p y Q₀ ∉ V.nonunits := evZ_not_mem_nonunits_of_isMinimalPrime hy hQ hQV hQ₀
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

omit hy in
include D in

theorem exists_ringHom_ker_eq_centre (i : Fin 2)
    (hred : ∃ red : ↥(D.W i) →+* LaurentSeries (ZMod p), ∀ f : ↥(D.W i), red f = 0 ↔ (f : F) ∈ (D.W i).nonunits) :
    ∃ θ : ↥(𝒪) →+* LaurentSeries (ZMod p), RingHom.ker θ = centre D i := by
  obtain ⟨red, hker⟩ := hred
  let incl : ↥(𝒪) →+* ↥(D.W i) :=
    { toFun := fun x => ⟨x, chartAlg_le_of_generic (D.generic i) x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨red.comp incl, ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, hker, mem_centre_iff]
  rfl

end Engine

section Instantiate

variable (N p)

set_option quotPrecheck false in
local notation "jF" => (jFull (N * p) : F)
set_option quotPrecheck false in
local notation "w" => atkinLehnerInvolutionFull N p

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

theorem exists_red_of_transform (W₀ W₁ : ValuationSubring F)
    (hW₁ : ∀ f : F, f ∈ W₁ ↔ w f ∈ W₀)
    (h₀ : ∃ red : ↥W₀ →+* LaurentSeries (ZMod p), ∀ f : ↥W₀, red f = 0 ↔ (f : F) ∈ W₀.nonunits) :
    ∃ red : ↥W₁ →+* LaurentSeries (ZMod p), ∀ f : ↥W₁, red f = 0 ↔ (f : F) ∈ W₁.nonunits := by
  obtain ⟨red₀, hker⟩ := h₀
  let wRes : ↥W₁ →+* ↥W₀ :=
    { toFun := fun f => ⟨w f, (hW₁ f).mp f.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  refine ⟨red₀.comp wRes, fun f => ?_⟩
  rw [RingHom.comp_apply, hker]
  change w (f : F) ∈ W₀.nonunits ↔ (f : F) ∈ W₁.nonunits
  rw [mem_nonunits_iff', mem_nonunits_iff', ← hW₁, ← map_inv₀, ← hW₁, map_eq_zero_iff _ (w).injective]

end Instantiate

end Setting

theorem main (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes,
      ∃ θ : ↥(chartAlgFin (N * p) p) →+* LaurentSeries (ZMod p), RingHom.ker θ = 𝔭) ∧
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf (N * p) p))}).minimalPrimes,
      ∃ θ : ↥(chartAlgInf (N * p) p) →+* LaurentSeries (ZMod p), RingHom.ker θ = 𝔭) := by
  obtain ⟨W, hW1, hW2, -, hW4, hW5⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N p hpN
  have hj0 : (jFull (N * p) : ↥(modularFunctionFieldFull (N * p))) ≠ 0 := jFull_ne_zero (N * p)
  have hgen : ∀ i, Generic N p (jFull (N * p)) (W i) := fun i => ⟨(hW4 i).1, (hW4 i).2.1⟩
  let D : BranchPair N p (jFull (N * p)) := ⟨W, hgen, fun V hV => hW5 V hV.1 hV.2⟩
  let D' : BranchPair N p (jFull (N * p))⁻¹ :=
    ⟨W, fun i => (hgen i).inv hj0, fun V hV => hW5 V hV.1 ((generic_inv_iff hj0 V).mp hV).2⟩
  have hyF := transcendental_jFull N p
  have hyI := transcendental_jFull_inv N p

  have hred0 : ∃ red : ↥(W 0) →+* LaurentSeries (ZMod p),
      ∀ f : ↥(W 0), red f = 0 ↔ (f : ↥(modularFunctionFieldFull (N * p))) ∈ (W 0).nonunits := by
    obtain ⟨red, hker, -⟩ :=
      ModularCurve.exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring p
        (modularFunctionFieldFull (N * p)) (W 0) hW1
    exact ⟨red, hker⟩
  have hred1 := exists_red_of_transform N p (W 0) (W 1) hW2 hred0
  have hred : ∀ i : Fin 2, ∃ red : ↥(W i) →+* LaurentSeries (ZMod p),
      ∀ f : ↥(W i), red f = 0 ↔ (f : ↥(modularFunctionFieldFull (N * p))) ∈ (W i).nonunits := by
    intro i
    fin_cases i
    · exact hred0
    · exact hred1
  refine ⟨fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rcases eq_centre_of_isMinimalPrime D hyF hQ with rfl | rfl
    · exact exists_ringHom_ker_eq_centre D 0 (hred 0)
    · exact exists_ringHom_ker_eq_centre D 1 (hred 1)
  · rcases eq_centre_of_isMinimalPrime D' hyI hQ with rfl | rfl
    · exact exists_ringHom_ker_eq_centre D' 0 (hred 0)
    · exact exists_ringHom_ker_eq_centre D' 1 (hred 1)

end IgusaBranchQExp
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd.IgusaBranchQExp"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd.IgusaBranchQExp"

open ModularCurve ModularCurve.IgusaScheme in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes,
      ∃ θ : ↥(chartAlgFin (N * p) p) →+* LaurentSeries (ZMod p), RingHom.ker θ = 𝔭) ∧
    (∀ 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgInf (N * p) p))}).minimalPrimes,
      ∃ θ : ↥(chartAlgInf (N * p) p) →+* LaurentSeries (ZMod p), RingHom.ker θ = 𝔭) :=
  IgusaBranchQExp.main N p hpN

end S_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd (solution)
