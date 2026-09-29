-- Prove2me | solution 1 for ModularCurve.DRModel.valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/055602c4-956c-5d4e-a58e-774abac7c76f

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_atkinLehnerInvolutionFull
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve AlgebraicCurve Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_one_apply qExpand_congr jq modularFunctionFieldFull jqd_mem_full IgusaScheme.jFull IgusaScheme coeffMap coeffMap_coeff coeffMap_jqModC jqModC jqModC_rat coeffMap_qExpand coeff_jqModC_pow_self coeff_jqModC_pow_of_lt IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd isIntegral_adjoin_jq_atkinLehnerInvolutionFull exists_isAtkinLehnerAutFull_of_prime_of_not_dvd qExpand_jqModC_eq_pow_unconditional atkinLehnerInvolutionFull_apply_apply"
namespace WUniqLevelP
p2m_open "ModularCurve"

def Statement (n : ℕ) [NeZero n] (p : ℕ) [Fact p.Prime] : Prop :=
    ∃ (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)))
      (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull n)),
      ((jp : ↥(modularFunctionFieldFull n)) : LaurentSeries ℚ) = qExpand ℚ p jq ∧
      ((p : ℕ) : ↥(modularFunctionFieldFull n)) ∈ W₀.nonunits ∧
      ((p : ℕ) : ↥(modularFunctionFieldFull n)) ∈ W₁.nonunits ∧
      W₀ ≠ W₁ ∧
      (∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P)⁻¹
            ∈ (![W₀, W₁] i)) ∧
      (∀ V : ValuationSubring ↥(modularFunctionFieldFull n),
        ((p : ℕ) : ↥(modularFunctionFieldFull n)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁) ∧
      ((jp : ↥(modularFunctionFieldFull n)) - (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) ^ p) ∈ W₀.nonunits ∧
      (∀ x : ↥(modularFunctionFieldFull n), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) Q
          - Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P
            ∈ W₀.nonunits) ∧
      (∀ x : ↥(modularFunctionFieldFull n), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (jp : ↥(modularFunctionFieldFull n)) Q
          - Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (jp : ↥(modularFunctionFieldFull n)) P
            ∈ W₁.nonunits)

theorem transport {n : ℕ} [NeZero n] (p : ℕ) [Fact p.Prime] [NeZero p] (h : n = p)
    (H : Statement n p) : Statement p p := by
  subst h
  exact H

section ValHelpers

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

end ValHelpers

section LevelOneMul

variable (p : ℕ) [hp : Fact p.Prime] [NeZero p]

abbrev Fld : Type := ↥(modularFunctionFieldFull (1 * p))

theorem not_dvd_one : ¬ p ∣ 1 := fun h => hp.out.ne_one (Nat.dvd_one.mp h)

abbrev jF : (Fld p) := IgusaScheme.jFull (1 * p)

def jpF : (Fld p) := ⟨qExpand ℚ p jq, jqd_mem_full (1 * p) (dvd_mul_left p 1)⟩

@[scoped simp] theorem coe_jpF_val : ((jpF p : (Fld p)) : LaurentSeries ℚ) = qExpand ℚ p jq := rfl

theorem isAL : IsAtkinLehnerAutFull 1 p (atkinLehnerInvolutionFull 1 p) :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull 1 p
    (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd 1 p hp.out (not_dvd_one p))

theorem w_jF : atkinLehnerInvolutionFull 1 p (jF p) = jpF p := by
  obtain ⟨h1, -⟩ := isAL p 1 inferInstance (one_dvd 1)
  have hjF : (jF p : (Fld p)) = ⟨qExpand ℚ 1 jq, jqd_mem_full (1 * p) (Dvd.dvd.mul_right (one_dvd 1) p)⟩ :=
    Subtype.ext (by change jq = qExpand ℚ 1 jq; rw [qExpand_one_apply])
  have hjpF : jpF p = ⟨qExpand ℚ (1 * p) jq, jqd_mem_full (1 * p) (Nat.mul_dvd_mul_right (one_dvd 1) p)⟩ :=
    Subtype.ext (by change qExpand ℚ p jq = qExpand ℚ (1 * p) jq; rw [qExpand_congr (one_mul p)])
  rw [hjF, hjpF]
  exact h1

theorem jpF_mem_chartAlgFin :
    jpF p ∈ TwoChartIntegralModel.chartAlgFin ℤ (Fld p) (jF p) := by
  rw [TwoChartIntegralModel.mem_chartAlg_iff]
  have hx : IsIntegral (Algebra.adjoin ℤ ({(jF p : (Fld p))} : Set (Fld p))) (jF p) := by
    have : (jF p : (Fld p)) = algebraMap (Algebra.adjoin ℤ ({(jF p : (Fld p))} : Set (Fld p))) (Fld p)
        ⟨jF p, Algebra.self_mem_adjoin_singleton ℤ _⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap
  have h := ModularCurve.isIntegral_adjoin_jq_atkinLehnerInvolutionFull 1 p (not_dvd_one p) ℤ (jF p) hx
  rwa [w_jF] at h

def jpChart : ↥(TwoChartIntegralModel.chartAlgFin ℤ (Fld p) (jF p)) := ⟨jpF p, jpF_mem_chartAlgFin p⟩

abbrev ιQ : LaurentSeries ℤ →+* LaurentSeries ℚ := coeffMap (Int.castRingHom ℚ)
abbrev ϖ : LaurentSeries ℤ →+* LaurentSeries (ZMod p) := coeffMap (Int.castRingHom (ZMod p))

theorem ιQ_injective : Function.Injective (ιQ) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries ℚ => s.coeff n) h
  simp only [coeffMap_coeff, eq_intCast, Int.cast_inj] at h1
  exact h1

def tZ : LaurentSeries ℤ := qExpand ℤ p (jqModC ℤ) - (jqModC ℤ) ^ p

theorem coe_jF : ((jF p : (Fld p)) : LaurentSeries ℚ) = ιQ (jqModC ℤ) := by
  change jq = _; rw [coeffMap_jqModC, jqModC_rat]

theorem coe_jpF : ((jpF p : (Fld p)) : LaurentSeries ℚ) = ιQ (qExpand ℤ p (jqModC ℤ)) := by
  change qExpand ℚ p jq = _; rw [coeffMap_qExpand, coeffMap_jqModC, jqModC_rat]

theorem coe_t : (((jpF p : (Fld p)) - (jF p) ^ p : (Fld p)) : LaurentSeries ℚ) = ιQ (tZ p) := by
  rw [tZ, map_sub, map_pow, ← coe_jpF p, ← coe_jF p]
  rfl

theorem ϖ_tZ : ϖ p (tZ p) = 0 := by
  rw [tZ, map_sub, map_pow, coeffMap_qExpand, coeffMap_jqModC,
    qExpand_jqModC_eq_pow_unconditional (ZMod p), sub_self]

theorem t_mem_nonunits (W₀ : ValuationSubring (Fld p))
    (hW₀ : ∀ f : (Fld p), f ∈ W₀ ↔ ∃ x y : LaurentSeries ℤ, ϖ p y ≠ 0 ∧ (f : LaurentSeries ℚ) * ιQ y = ιQ x) :
    ((jpF p : (Fld p)) - (jF p) ^ p) ∈ W₀.nonunits := by
  have h1 : ϖ p 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  rw [mem_nonunits_iff']
  refine ⟨(hW₀ _).mpr ⟨tZ p, 1, h1, by rw [map_one, mul_one, coe_t]⟩, ?_⟩
  by_cases h0 : ((jpF p : (Fld p)) - (jF p) ^ p) = 0
  · exact Or.inl h0
  · right
    rintro hinv
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ _).mp hinv
    apply hy
    have ht0 : (((jpF p : (Fld p)) - (jF p) ^ p : (Fld p)) : LaurentSeries ℚ) ≠ 0 := fun e => h0 (Subtype.ext e)
    have : ιQ y = ιQ (tZ p * x) := by
      rw [map_mul, ← hxy, ← coe_t p, IntermediateField.coe_inv, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
    rw [ιQ_injective this, map_mul, ϖ_tZ, zero_mul]

theorem w_jpF : atkinLehnerInvolutionFull 1 p (jpF p) = jF p := by
  obtain ⟨-, h2⟩ := isAL p 1 inferInstance (one_dvd 1)
  have hjF : (jF p : (Fld p)) = ⟨qExpand ℚ 1 jq, jqd_mem_full (1 * p) (Dvd.dvd.mul_right (one_dvd 1) p)⟩ :=
    Subtype.ext (by change jq = qExpand ℚ 1 jq; rw [qExpand_one_apply])
  have hjpF : jpF p = ⟨qExpand ℚ (1 * p) jq, jqd_mem_full (1 * p) (Nat.mul_dvd_mul_right (one_dvd 1) p)⟩ :=
    Subtype.ext (by change qExpand ℚ p jq = qExpand ℚ (1 * p) jq; rw [qExpand_congr (one_mul p)])
  rw [hjF, hjpF]
  exact h2

def tZ' : LaurentSeries ℤ := jqModC ℤ - (qExpand ℤ p (jqModC ℤ)) ^ p

theorem w_t : atkinLehnerInvolutionFull 1 p ((jpF p : (Fld p)) - (jF p) ^ p) = (jF p : (Fld p)) - (jpF p) ^ p := by
  rw [map_sub, map_pow, w_jpF, w_jF]

theorem coe_w_t : ((atkinLehnerInvolutionFull 1 p ((jpF p : (Fld p)) - (jF p) ^ p) : (Fld p)) : LaurentSeries ℚ) = ιQ (tZ' p) := by
  rw [w_t, tZ', map_sub, map_pow, ← coe_jpF p, ← coe_jF p]
  rfl

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
    push_neg at hlt
    exact (fun h0 => hne (HahnSeries.coeff_order_eq_zero.mp h0)) (coeff_jqModC_pow_of_lt (ZMod p) hlt)
  rw [ho, ho] at h1
  have hp1 : 1 < p := hp.out.one_lt
  have h2 : ((p * p : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by linarith
  have h3 : p * p = 1 := by exact_mod_cast h2
  nlinarith

theorem w_t_ne_zero : atkinLehnerInvolutionFull 1 p ((jpF p : (Fld p)) - (jF p) ^ p) ≠ 0 := by
  intro h0
  have h1 : ((atkinLehnerInvolutionFull 1 p ((jpF p : (Fld p)) - (jF p) ^ p) : (Fld p)) : LaurentSeries ℚ) = 0 := by
    rw [h0]; rfl
  rw [coe_w_t] at h1
  exact ϖ_tZ'_ne_zero p (by rw [ιQ_injective (h1.trans (map_zero _).symm), map_zero])

theorem t_ne_zero : ((jpF p : (Fld p)) - (jF p) ^ p) ≠ 0 := fun h =>
  w_t_ne_zero p (by rw [h, map_zero])

theorem inv_w_t_mem_gauss (W₀ : ValuationSubring (Fld p))
    (hW₀ : ∀ f : (Fld p), f ∈ W₀ ↔ ∃ x y : LaurentSeries ℤ, ϖ p y ≠ 0 ∧ (f : LaurentSeries ℚ) * ιQ y = ιQ x) :
    (atkinLehnerInvolutionFull 1 p ((jpF p : (Fld p)) - (jF p) ^ p))⁻¹ ∈ W₀ := by
  refine (hW₀ _).mpr ⟨1, tZ' p, ϖ_tZ'_ne_zero p, ?_⟩
  have ht0 : ((atkinLehnerInvolutionFull 1 p ((jpF p : (Fld p)) - (jF p) ^ p) : (Fld p)) : LaurentSeries ℚ) ≠ 0 :=
    fun e => w_t_ne_zero p (Subtype.ext e)
  rw [IntermediateField.coe_inv, ← coe_w_t p, inv_mul_cancel₀ ht0, map_one]

def UStatement (n : ℕ) [NeZero n] (p : ℕ) [Fact p.Prime] : Prop :=
    ∀ (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull n) (IgusaScheme.jFull n)))
      (_hjp : ((jp : ↥(modularFunctionFieldFull n)) : LaurentSeries ℚ) = qExpand ℚ p jq)
      (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull n))
      (_hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull n)) ∈ W₀.nonunits)
      (_hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull n)) ∈ W₁.nonunits)
      (_hne : W₀ ≠ W₁)
      (_hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P)⁻¹
            ∈ (![W₀, W₁] i))
      (_hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull n),
        ((p : ℕ) : ↥(modularFunctionFieldFull n)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull n)) (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
      (_ht : ((jp : ↥(modularFunctionFieldFull n)) - (IgusaScheme.jFull n : ↥(modularFunctionFieldFull n)) ^ p) ∈ W₀.nonunits),
    (∀ f : ↥(modularFunctionFieldFull n), f ∈ W₀ ↔
        ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) ∧
    (∃ σ : ↥(modularFunctionFieldFull n) ≃ₐ[ℚ] ↥(modularFunctionFieldFull n),
        σ (IgusaScheme.jFull n) = (jp : ↥(modularFunctionFieldFull n)) ∧ σ (jp : ↥(modularFunctionFieldFull n)) = IgusaScheme.jFull n ∧
        (∀ f : ↥(modularFunctionFieldFull n), σ (σ f) = f) ∧
        (∀ f : ↥(modularFunctionFieldFull n), f ∈ W₁ ↔ σ f ∈ W₀))

omit hp [NeZero p] in
theorem transportU {n : ℕ} [NeZero n] [Fact p.Prime] [NeZero p] (h : n = p)
    (H : UStatement n p) : UStatement p p := by
  subst h
  exact H

theorem level_one_mul_U : UStatement (1 * p) p := by
  intro jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht
  obtain ⟨W, hW1, hW2, -, hW4, hW5⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd 1 p (not_dvd_one p)
  have hjp' : (jp : (Fld p)) = jpF p := Subtype.ext hjp
  have hgen₀ : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ (Fld p)) (jF p : (Fld p)) P ∈ W₀ ∧
      (Polynomial.eval₂ (algebraMap ℤ (Fld p)) (jF p : (Fld p)) P)⁻¹ ∈ W₀ := fun P hP => hgen 0 P hP
  have hgen₁ : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      Polynomial.eval₂ (algebraMap ℤ (Fld p)) (jF p : (Fld p)) P ∈ W₁ ∧
      (Polynomial.eval₂ (algebraMap ℤ (Fld p)) (jF p : (Fld p)) P)⁻¹ ∈ W₁ := fun P hP => hgen 1 P hP
  have hW₀ : W₀ = W 0 ∨ W₀ = W 1 := hW5 W₀ hp₀ hgen₀
  have hW₁ : W₁ = W 0 ∨ W₁ = W 1 := hW5 W₁ hp₁ hgen₁

  have ht1 : ((jpF p : (Fld p)) - (jF p) ^ p) ∉ (W 1).nonunits := by
    apply not_mem_nonunits_of_inv_mem _ (t_ne_zero p)
    rw [hW2, map_inv₀]
    exact inv_w_t_mem_gauss p (W 0) hW1
  have h0 : W₀ = W 0 := by
    rcases hW₀ with h | h
    · exact h
    · exfalso
      rw [h, hjp'] at ht
      exact ht1 ht
  have h1 : W₁ = W 1 := by
    rcases hW₁ with h | h
    · exact absurd (h0.trans h.symm) hne
    · exact h
  refine ⟨?_, ?_⟩
  · intro f
    rw [h0]
    exact hW1 f
  · refine ⟨atkinLehnerInvolutionFull 1 p, ?_, ?_, ?_, ?_⟩
    · rw [hjp']; exact w_jF p
    · rw [hjp']; exact w_jpF p
    · exact fun f => ModularCurve.atkinLehnerInvolutionFull_apply_apply 1 p (not_dvd_one p) f
    · intro f
      rw [h1, h0]
      exact hW2 f

end LevelOneMul

end ModularCurve.WUniqLevelP
p2m_reactivate "P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve.WUniqLevelP"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve.WUniqLevelP"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve in
theorem solution (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits) :

    (∀ f : ↥(modularFunctionFieldFull p), f ∈ W₀ ↔
        ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) ∧

    (∃ σ : ↥(modularFunctionFieldFull p) ≃ₐ[ℚ] ↥(modularFunctionFieldFull p),
        σ (IgusaScheme.jFull p) = (jp : ↥(modularFunctionFieldFull p)) ∧ σ (jp : ↥(modularFunctionFieldFull p)) = IgusaScheme.jFull p ∧
        (∀ f : ↥(modularFunctionFieldFull p), σ (σ f) = f) ∧
        (∀ f : ↥(modularFunctionFieldFull p), f ∈ W₁ ↔ σ f ∈ W₀)) :=
  ModularCurve.WUniqLevelP.transportU p (Nat.one_mul p) (ModularCurve.WUniqLevelP.level_one_mul_U p)
    jp hjp W₀ W₁ hp₀ hp₁ hne hgen hcomplete ht

end S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap
end P2MW
export P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap (solution)
