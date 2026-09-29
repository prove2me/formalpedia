-- Prove2me | solution 1 for ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e9cc2191-321e-5274-abc6-6f81c2156d37

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
open IntermediateField AlgebraicCurve ModularCurve Polynomial

namespace NeronLeg1TwoBranchesQ

section IntSeries

abbrev ιK (K : Type*) [CommRing K] : LaurentSeries ℤ →+* LaurentSeries K :=
  coeffMap (Int.castRingHom K)

variable (p : ℕ) [Fact p.Prime]

abbrev ϖ : LaurentSeries ℤ →+* LaurentSeries (ZMod p) := coeffMap (Int.castRingHom (ZMod p))

theorem ιK_injective (K : Type*) [CommRing K] [CharZero K] : Function.Injective (ιK K) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff n) h
  simp only [coeffMap_coeff, eq_intCast, Int.cast_inj] at h1
  exact h1

theorem ιK_eq_zero_iff (K : Type*) [CommRing K] [CharZero K] (x : LaurentSeries ℤ) :
    ιK K x = 0 ↔ x = 0 := by
  rw [← map_zero (ιK K)]; exact (ιK_injective K).eq_iff

theorem ϖ_eq_zero_iff (y : LaurentSeries ℤ) : ϖ p y = 0 ↔ ∀ n, (p : ℤ) ∣ y.coeff n := by
  constructor
  · intro h n
    have h1 := congrArg (fun s : LaurentSeries (ZMod p) => s.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero, eq_intCast] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1
  · intro h
    ext n
    simp only [coeffMap_coeff, HahnSeries.coeff_zero, eq_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h n)

def divCoeff (x : LaurentSeries ℤ) (d : ℤ) : LaurentSeries ℤ where
  coeff n := x.coeff n / d
  isPWO_support' := x.isPWO_support'.mono (by
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h0; apply hn; rw [h0, Int.zero_ediv])

@[scoped simp] theorem divCoeff_coeff (x : LaurentSeries ℤ) (d : ℤ) (n : ℤ) :
    (divCoeff x d).coeff n = x.coeff n / d := rfl

theorem C_mul_divCoeff {x : LaurentSeries ℤ} {d : ℤ} (h : ∀ n, d ∣ x.coeff n) :
    HahnSeries.C d * divCoeff x d = x := by
  ext n
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, divCoeff_coeff, smul_eq_mul,
    Int.mul_ediv_cancel' (h n)]

theorem exists_pContent {x : LaurentSeries ℤ} (hx : x ≠ 0) :
    ∃ (a : ℕ) (x₀ : LaurentSeries ℤ), x = HahnSeries.C ((p : ℤ) ^ a) * x₀ ∧ ϖ p x₀ ≠ 0 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt

  have hex : ∃ a : ℕ, ∃ n : ℤ, ¬ ((p : ℤ) ^ (a + 1) ∣ x.coeff n) := by
    obtain ⟨n, hn⟩ : ∃ n, x.coeff n ≠ 0 := by
      by_contra h; push Not at h; exact hx (HahnSeries.ext (funext h))
    refine ⟨(x.coeff n).natAbs, n, fun hdvd => ?_⟩
    have hle := Int.le_of_dvd (Int.natAbs_pos.mpr hn |> fun h => by
      exact abs_pos.mpr hn) ((Int.dvd_natAbs).mpr hdvd |> fun h => by
      simpa using (Int.dvd_natAbs.mpr hdvd))
    have hlt : ((x.coeff n).natAbs : ℤ) < (p : ℤ) ^ ((x.coeff n).natAbs + 1) := by
      have h1 : (x.coeff n).natAbs < p ^ ((x.coeff n).natAbs + 1) :=
        (Nat.lt_pow_self hp1).trans (Nat.pow_lt_pow_right hp1 (Nat.lt_succ_self _))
      exact_mod_cast h1
    rw [Int.natCast_natAbs] at hlt
    exact absurd (hle.trans_lt hlt) (lt_irrefl _)
  let a := Nat.find hex
  obtain ⟨n₀, hn₀⟩ : ∃ n, ¬ ((p : ℤ) ^ (a + 1) ∣ x.coeff n) := Nat.find_spec hex
  have hall : ∀ n, (p : ℤ) ^ a ∣ x.coeff n := by
    intro n
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, pow_zero]; exact one_dvd _
    · have hmin := Nat.find_min hex (m := a - 1) (by omega)
      push Not at hmin
      have := hmin n
      rwa [Nat.sub_add_cancel ha] at this
  refine ⟨a, divCoeff x ((p : ℤ) ^ a), (C_mul_divCoeff hall).symm, ?_⟩
  rw [Ne, ϖ_eq_zero_iff]
  intro hdvd
  apply hn₀
  have h1 := hdvd n₀
  rw [divCoeff_coeff] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : x.coeff n₀ = (p : ℤ) ^ a * (x.coeff n₀ / (p : ℤ) ^ a) :=
    (Int.mul_ediv_cancel' (hall n₀)).symm
  rw [h2, hc, pow_succ]; exact ⟨c, by ring⟩

theorem exists_eq_C_mul_of_ϖ_eq_zero {x : LaurentSeries ℤ} (h : ϖ p x = 0) :
    ∃ x' : LaurentSeries ℤ, x = HahnSeries.C (p : ℤ) * x' :=
  ⟨divCoeff x p, (C_mul_divCoeff ((ϖ_eq_zero_iff p x).mp h)).symm⟩

theorem ιK_C (K : Type*) [Field K] (c : ℤ) :
    ιK K (HahnSeries.C c) = algebraMap K (LaurentSeries K) (c : K) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]; simp

theorem ϖ_C (c : ℤ) : ϖ p (HahnSeries.C c) = HahnSeries.C (c : ZMod p) := by
  rw [HahnSeries.C_apply, coeffMap_single, HahnSeries.C_apply]; simp

end IntSeries

section GaussZ

variable (p : ℕ) [Fact p.Prime]

def IsGaussZ (f : LaurentSeries ℚ) : Prop :=
  ∃ x y : LaurentSeries ℤ, ϖ p y ≠ 0 ∧ f * ιK ℚ y = ιK ℚ x

variable {p}

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries ℤ} (hy : ϖ p y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

theorem ιK_ne_zero_of_ϖ {y : LaurentSeries ℤ} (hy : ϖ p y ≠ 0) : ιK ℚ y ≠ 0 := by
  rw [Ne, ιK_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hy

theorem IsGaussZ.one : IsGaussZ p (1 : LaurentSeries ℚ) := ⟨1, 1, by simp, by simp⟩

theorem IsGaussZ.mul {f g : LaurentSeries ℚ} (hf : IsGaussZ p f) (hg : IsGaussZ p g) :
    IsGaussZ p (f * g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * x', y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsGaussZ.inv_of {f : LaurentSeries ℚ} {x y : LaurentSeries ℤ} (hx : ϖ p x ≠ 0)
    (h : f * ιK ℚ y = ιK ℚ x) (_hy : ϖ p y ≠ 0) : IsGaussZ p f⁻¹ := by
  have hf : f ≠ 0 := by
    rintro rfl; rw [zero_mul] at h; exact ιK_ne_zero_of_ϖ hx h.symm
  refine ⟨y, x, hx, ?_⟩
  rw [← h]; field_simp

theorem IsGaussZ.ϖ_ne_zero_of_inv {f : LaurentSeries ℚ} (hf : f ≠ 0) {x y : LaurentSeries ℤ}
    (hy : ϖ p y ≠ 0) (h : f * ιK ℚ y = ιK ℚ x) (hinv : IsGaussZ p f⁻¹) : ϖ p x ≠ 0 := by
  obtain ⟨x', y', hy', h'⟩ := hinv

  have hprod : ιK ℚ (y * y') = ιK ℚ (x * x') := by
    rw [map_mul, map_mul, ← h, ← h']; field_simp
  have hprod' : y * y' = x * x' := ιK_injective ℚ hprod
  intro hx
  have h0 : ϖ p (y * y') = 0 := by rw [hprod', map_mul, hx, zero_mul]
  rw [map_mul] at h0
  exact mul_ne_zero hy hy' h0

end GaussZ

section FieldF

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]

set_option quotPrecheck false in
local notation "FQ" => (↥(modularFunctionFieldFull M) : Type)

theorem exists_intFrac (f : FQ) :
    ∃ P Q : LaurentSeries ℤ, Q ≠ 0 ∧ ιK ℚ P ∈ modularFunctionFieldFull M ∧
      ιK ℚ Q ∈ modularFunctionFieldFull M ∧ (f : LaurentSeries ℚ) * ιK ℚ Q = ιK ℚ P := by
  let S : Subfield (LaurentSeries ℚ) :=
    { carrier := {g | ∃ P Q : LaurentSeries ℤ, Q ≠ 0 ∧ ιK ℚ P ∈ modularFunctionFieldFull M ∧
        ιK ℚ Q ∈ modularFunctionFieldFull M ∧ g * ιK ℚ Q = ιK ℚ P}
      mul_mem' := by
        rintro g g' ⟨P, Q, hQ, hPF, hQF, h⟩ ⟨P', Q', hQ', hPF', hQF', h'⟩
        refine ⟨P * P', Q * Q', mul_ne_zero hQ hQ', ?_, ?_, ?_⟩
        · rw [map_mul]; exact mul_mem hPF hPF'
        · rw [map_mul]; exact mul_mem hQF hQF'
        rw [map_mul, map_mul, ← h, ← h']; ring
      one_mem' := ⟨1, 1, one_ne_zero, by rw [map_one]; exact one_mem _, by rw [map_one]; exact one_mem _, by simp⟩
      add_mem' := by
        rintro g g' ⟨P, Q, hQ, hPF, hQF, h⟩ ⟨P', Q', hQ', hPF', hQF', h'⟩
        refine ⟨P * Q' + P' * Q, Q * Q', mul_ne_zero hQ hQ', ?_, ?_, ?_⟩
        · rw [map_add, map_mul, map_mul]; exact add_mem (mul_mem hPF hQF') (mul_mem hPF' hQF)
        · rw [map_mul]; exact mul_mem hQF hQF'
        rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring
      zero_mem' := ⟨0, 1, one_ne_zero, by rw [map_zero]; exact zero_mem _, by rw [map_one]; exact one_mem _, by simp⟩
      neg_mem' := by
        rintro g ⟨P, Q, hQ, hPF, hQF, h⟩
        exact ⟨-P, Q, hQ, by rw [map_neg]; exact neg_mem hPF, hQF, by rw [map_neg, ← h]; ring⟩
      inv_mem' := by
        rintro g ⟨P, Q, hQ, hPF, hQF, h⟩
        by_cases hg : g = 0
        · exact ⟨0, 1, one_ne_zero, by rw [map_zero]; exact zero_mem _, by rw [map_one]; exact one_mem _, by simp [hg]⟩
        have hP : P ≠ 0 := by
          rintro rfl
          rw [map_zero] at h
          exact (mul_ne_zero hg ((ιK_eq_zero_iff ℚ Q).not.mpr hQ)) h
        refine ⟨Q, P, hP, hQF, hPF, ?_⟩
        rw [← h]; field_simp }
  have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M)
      ≤ S := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | ⟨d, hd, hdM, rfl⟩)
    · refine ⟨HahnSeries.C t.num, HahnSeries.C (t.den : ℤ), ?_, ?_, ?_, ?_⟩
      · exact HahnSeries.C_ne_zero (by exact_mod_cast t.den_ne_zero)
      · rw [ιK_C]; exact (modularFunctionFieldFull M).algebraMap_mem _
      · rw [ιK_C]; exact (modularFunctionFieldFull M).algebraMap_mem _
      · rw [ιK_C, ιK_C, ← map_mul]
        congr 1
        push_cast
        exact Rat.mul_den_eq_num t
    · haveI := hd
      refine ⟨qExpand ℤ d (jqModC ℤ), 1, one_ne_zero, ?_, by rw [map_one]; exact one_mem _, ?_⟩
      · rw [coeffMap_qExpand, coeffMap_jqModC, jqModC_rat]; exact jqd_mem_full M hdM
      · rw [map_one, mul_one, coeffMap_qExpand, coeffMap_jqModC, jqModC_rat]
  obtain ⟨P, Q, hQ, hPF, hQF, h⟩ := hle (show (f : LaurentSeries ℚ) ∈ Subfield.closure _ from f.2)
  exact ⟨P, Q, hQ, hPF, hQF, h⟩

variable {p M}

theorem ιK_mem_of_C_mul {x x₀ : LaurentSeries ℤ} {a : ℕ} (hx : x = HahnSeries.C ((p : ℤ) ^ a) * x₀)
    (hxF : ιK ℚ x ∈ modularFunctionFieldFull M) : ιK ℚ x₀ ∈ modularFunctionFieldFull M := by
  have hpa : ((((p : ℤ) ^ a : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast pow_ne_zero a (Fact.out : p.Prime).ne_zero
  have h1 : ιK ℚ x₀ = algebraMap ℚ (LaurentSeries ℚ) ((((p : ℤ) ^ a : ℤ) : ℚ)⁻¹) * ιK ℚ x := by
    rw [hx, map_mul, ιK_C, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hpa, map_one, one_mul]
  rw [h1]
  exact mul_mem ((modularFunctionFieldFull M).algebraMap_mem _) hxF

theorem exists_pFrac {f : FQ} (hf : f ≠ 0) :
    ∃ (a b : ℕ) (P₀ Q₀ : LaurentSeries ℤ), ϖ p P₀ ≠ 0 ∧ ϖ p Q₀ ≠ 0 ∧
      ιK ℚ P₀ ∈ modularFunctionFieldFull M ∧ ιK ℚ Q₀ ∈ modularFunctionFieldFull M ∧
      (f : LaurentSeries ℚ) * ιK ℚ Q₀ * algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ b)
        = algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ a) * ιK ℚ P₀ := by
  obtain ⟨P, Q, hQ, hPF, hQF, h⟩ := exists_intFrac M f
  have hf' : (f : LaurentSeries ℚ) ≠ 0 := fun h0 => hf (Subtype.ext h0)
  have hP : P ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact (mul_ne_zero hf' ((ιK_eq_zero_iff ℚ Q).not.mpr hQ)) h
  obtain ⟨a, P₀, hP₀, hP₀'⟩ := exists_pContent p hP
  obtain ⟨b, Q₀, hQ₀, hQ₀'⟩ := exists_pContent p hQ
  refine ⟨a, b, P₀, Q₀, hP₀', hQ₀', ιK_mem_of_C_mul hP₀ hPF, ιK_mem_of_C_mul hQ₀ hQF, ?_⟩
  have h1 : ιK ℚ Q = algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ b) * ιK ℚ Q₀ := by
    rw [hQ₀, map_mul, ιK_C]; push_cast; ring
  have h2 : ιK ℚ P = algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ a) * ιK ℚ P₀ := by
    rw [hP₀, map_mul, ιK_C]; push_cast; ring
  calc (f : LaurentSeries ℚ) * ιK ℚ Q₀ * algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ b)
      = (f : LaurentSeries ℚ) * ιK ℚ Q := by rw [h1]; ring
    _ = _ := by rw [h, h2]

theorem isGaussZ_of_pFrac {f : LaurentSeries ℚ} {a b : ℕ} {P₀ Q₀ : LaurentSeries ℤ}
    (hQ₀ : ϖ p Q₀ ≠ 0)
    (h : f * ιK ℚ Q₀ * algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ b)
        = algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ a) * ιK ℚ P₀) (hab : b ≤ a) :
    IsGaussZ p f := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set π : LaurentSeries ℚ := algebraMap ℚ (LaurentSeries ℚ) (p : ℚ) with hπ
  have hπ0 : π ≠ 0 := (_root_.map_ne_zero _).mpr hp0
  rw [map_pow, map_pow] at h
  have hιC : ∀ n : ℕ, ιK ℚ (HahnSeries.C ((p : ℤ) ^ n)) = π ^ n := by
    intro n; rw [ιK_C, hπ, ← map_pow]; push_cast; rfl
  refine ⟨HahnSeries.C ((p : ℤ) ^ (a - b)) * P₀, Q₀, hQ₀, ?_⟩
  rw [map_mul, hιC]
  apply mul_right_cancel₀ (pow_ne_zero b hπ0)
  rw [h, mul_assoc, mul_comm (ιK ℚ P₀) (π ^ b), ← mul_assoc, pow_sub_mul_pow π hab]

variable (p M)

def gaussZ : ValuationSubring FQ where
  carrier := {f | IsGaussZ p (f : LaurentSeries ℚ)}
  mul_mem' {f g} hf hg := by
    change IsGaussZ p ((f * g : FQ) : LaurentSeries ℚ)
    rw [IntermediateField.coe_mul]; exact hf.mul hg
  one_mem' := by change IsGaussZ p ((1 : FQ) : LaurentSeries ℚ); exact IsGaussZ.one
  add_mem' {f g} hf hg := by
    change IsGaussZ p ((f + g : FQ) : LaurentSeries ℚ)
    obtain ⟨x, y, hy, h⟩ := hf
    obtain ⟨x', y', hy', h'⟩ := hg
    refine ⟨x * y' + x' * y, y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
    rw [IntermediateField.coe_add, map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  neg_mem' {f} hf := by
    change IsGaussZ p ((-f : FQ) : LaurentSeries ℚ)
    obtain ⟨x, y, hy, h⟩ := hf
    exact ⟨-x, y, hy, by rw [IntermediateField.coe_neg, map_neg, ← h]; ring⟩
  mem_or_inv_mem' f := by
    by_cases hf : f = 0
    · left; subst hf; exact ⟨0, 1, by simp, by simp⟩
    obtain ⟨a, b, P₀, Q₀, hP₀, hQ₀, -, -, h⟩ := exists_pFrac (p := p) hf
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    set π : LaurentSeries ℚ := algebraMap ℚ (LaurentSeries ℚ) (p : ℚ) with hπ
    have hπ0 : π ≠ 0 := (_root_.map_ne_zero _).mpr hp0
    rw [map_pow, map_pow] at h
    have hιC : ∀ n : ℕ, ιK ℚ (HahnSeries.C ((p : ℤ) ^ n)) = π ^ n := by
      intro n; rw [ιK_C, hπ, ← map_pow]; push_cast; rfl
    rcases le_or_gt b a with hab | hab
    · left
      refine ⟨HahnSeries.C ((p : ℤ) ^ (a - b)) * P₀, Q₀, hQ₀, ?_⟩
      rw [map_mul, hιC]
      apply mul_right_cancel₀ (pow_ne_zero b hπ0)
      rw [h, mul_assoc, mul_comm (ιK ℚ P₀) (π ^ b), ← mul_assoc, pow_sub_mul_pow π hab]
    · right
      change IsGaussZ p ((f⁻¹ : FQ) : LaurentSeries ℚ)
      rw [IntermediateField.coe_inv]
      refine ⟨HahnSeries.C ((p : ℤ) ^ (b - a)) * Q₀, P₀, hP₀, ?_⟩
      rw [map_mul, hιC]
      have hf' : (f : LaurentSeries ℚ) ≠ 0 := fun h0 => hf (Subtype.ext h0)
      apply mul_right_cancel₀ (pow_ne_zero a hπ0)
      apply mul_left_cancel₀ hf'
      calc (f : LaurentSeries ℚ) * ((f : LaurentSeries ℚ)⁻¹ * ιK ℚ P₀ * π ^ a)
          = π ^ a * ιK ℚ P₀ := by field_simp
        _ = (f : LaurentSeries ℚ) * ιK ℚ Q₀ * π ^ b := h.symm
        _ = (f : LaurentSeries ℚ) * ιK ℚ Q₀ * (π ^ (b - a) * π ^ a) := by
              rw [pow_sub_mul_pow π hab.le]
        _ = _ := by ring

theorem mem_gaussZ_iff (f : FQ) : f ∈ gaussZ p M ↔ IsGaussZ p (f : LaurentSeries ℚ) := Iff.rfl

variable {p M}

theorem isUnit_iff_inv_mem {K : Type*} [Field K] (A : ValuationSubring K) {a : K} (ha : a ∈ A)
    (ha0 : a ≠ 0) : IsUnit (⟨a, ha⟩ : A) ↔ a⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : ((↑u⁻¹ : A) : K) * a = 1 := by
      have := congrArg (fun y : A => (y : K)) u.inv_mul
      simpa [hu] using this
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ ha0),
      Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

theorem mem_nonunits_iff' {K : Type*} [Field K] (A : ValuationSubring K) (a : K) :
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

variable (p M)

theorem coe_pF : ((((p : ℕ) : FQ)) : LaurentSeries ℚ) = ιK ℚ (HahnSeries.C (p : ℤ)) := by
  rw [ιK_C]; push_cast; rfl

theorem p_mem_nonunits_gaussZ : ((p : ℕ) : FQ) ∈ (gaussZ p M).nonunits := by
  rw [mem_nonunits_iff']
  refine ⟨⟨HahnSeries.C (p : ℤ), 1, by simp, by rw [map_one, mul_one, coe_pF]⟩, Or.inr ?_⟩
  rintro ⟨x, y, hy, h⟩
  rw [IntermediateField.coe_inv, coe_pF, ιK_C] at h
  have hpQ : (algebraMap ℚ (LaurentSeries ℚ)) ((p : ℤ) : ℚ) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h2 : ιK ℚ y = ιK ℚ (HahnSeries.C (p : ℤ) * x) := by
    rw [map_mul, ιK_C, ← h, ← mul_assoc, mul_inv_cancel₀ hpQ, one_mul]
  have h3 : y = HahnSeries.C (p : ℤ) * x := ιK_injective ℚ h2
  apply hy
  rw [h3, map_mul, ϖ_C]; simp

theorem mul_inv_p_mem_gaussZ (f : FQ) (hf : f ∈ (gaussZ p M).nonunits) :
    f * ((p : ℕ) : FQ)⁻¹ ∈ gaussZ p M := by
  rw [mem_nonunits_iff'] at hf
  obtain ⟨⟨x, y, hy, h⟩, h0⟩ := hf
  rcases h0 with h0 | hinv
  · rw [h0, zero_mul]; exact zero_mem _
  ·
    have hx : ϖ p x = 0 := by
      by_contra hx
      exact hinv (by
        change IsGaussZ p ((f⁻¹ : FQ) : LaurentSeries ℚ)
        rw [IntermediateField.coe_inv]; exact IsGaussZ.inv_of hx h hy)
    obtain ⟨x', hx'⟩ := exists_eq_C_mul_of_ϖ_eq_zero p hx
    refine ⟨x', y, hy, ?_⟩
    have hpQ : (algebraMap ℚ (LaurentSeries ℚ)) ((p : ℤ) : ℚ) ≠ 0 :=
      (_root_.map_ne_zero _).mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    rw [IntermediateField.coe_mul, IntermediateField.coe_inv, coe_pF, ιK_C, mul_right_comm, h, hx',
      map_mul, ιK_C]
    field_simp

end FieldF

section Generators

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "FQ" => (↥(modularFunctionFieldFull (N * p)) : Type)

scoped instance instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

def jFQ : FQ := ⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩

def jpFQ : FQ := ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩

@[scoped simp] theorem coe_jFQ : ((jFQ N p : FQ) : LaurentSeries ℚ) = ιK ℚ (jqModC ℤ) := by
  change jq = _; rw [coeffMap_jqModC, jqModC_rat]

@[scoped simp] theorem coe_jpFQ : ((jpFQ N p : FQ) : LaurentSeries ℚ) = ιK ℚ (qExpand ℤ p (jqModC ℤ)) := by
  change qExpand ℚ p jq = _; rw [coeffMap_qExpand, coeffMap_jqModC, jqModC_rat]

theorem coe_eval₂ (P : Polynomial ℤ) (g : FQ) (z : LaurentSeries ℤ) (hg : (g : LaurentSeries ℚ) = ιK ℚ z) :
    ((P.eval₂ (algebraMap ℤ FQ) g : FQ) : LaurentSeries ℚ) = ιK ℚ (P.eval₂ (algebraMap ℤ _) z) := by
  have h1 := Polynomial.hom_eval₂ P (algebraMap ℤ FQ)
    ((modularFunctionFieldFull (N * p)).val : FQ →+* LaurentSeries ℚ) g
  change ((modularFunctionFieldFull (N * p)).val : FQ →+* LaurentSeries ℚ) (P.eval₂ (algebraMap ℤ FQ) g) = _
  rw [h1, Polynomial.hom_eval₂]
  change P.eval₂ _ (g : LaurentSeries ℚ) = _
  rw [hg]
  congr 1
  exact RingHom.ext_int _ _

theorem ϖ_eval₂ (P : Polynomial ℤ) (z : LaurentSeries ℤ) :
    ϖ p (P.eval₂ (algebraMap ℤ _) z) = (P.map (Int.castRingHom (ZMod p))).eval₂
      (algebraMap (ZMod p) (LaurentSeries (ZMod p))) (ϖ p z) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem eval₂_jqModC_ne_zero {Q : Polynomial (ZMod p)} (hQ : Q ≠ 0) :
    Q.eval₂ (algebraMap (ZMod p) (LaurentSeries (ZMod p))) (jqModC (ZMod p)) ≠ 0 := by
  intro h
  exact ModularCurve.transcendental_jqModC (ZMod p) ⟨Q, hQ, by rwa [Polynomial.aeval_def]⟩

theorem eval₂_qExpand_jqModC_ne_zero {Q : Polynomial (ZMod p)} (hQ : Q ≠ 0) :
    Q.eval₂ (algebraMap (ZMod p) (LaurentSeries (ZMod p))) (qExpand (ZMod p) p (jqModC (ZMod p)))
      ≠ 0 := by
  intro h
  have halg : IsAlgebraic (ZMod p) (qExpandAlgHomC (ZMod p) p (jqModC (ZMod p))) :=
    ⟨Q, hQ, by rw [Polynomial.aeval_def]; exact h⟩
  exact ModularCurve.transcendental_jqModC (ZMod p)
    ((isAlgebraic_algHom_iff (qExpandAlgHomC (ZMod p) p)
      (qExpand_injective (R := ZMod p) (N := p))).mp halg)

variable {N p}

theorem eval₂_mem_and_inv_mem_gaussZ {P : Polynomial ℤ} (hP : P.map (Int.castRingHom (ZMod p)) ≠ 0)
    (g : FQ) (z : LaurentSeries ℤ) (hg : (g : LaurentSeries ℚ) = ιK ℚ z)
    (hz : ∀ {Q : Polynomial (ZMod p)}, Q ≠ 0 →
      Q.eval₂ (algebraMap (ZMod p) (LaurentSeries (ZMod p))) (ϖ p z) ≠ 0) :
    P.eval₂ (algebraMap ℤ FQ) g ∈ gaussZ p (N * p) ∧
      (P.eval₂ (algebraMap ℤ FQ) g)⁻¹ ∈ gaussZ p (N * p) := by
  have hcoe := coe_eval₂ N p P g z hg
  have hred : ϖ p (P.eval₂ (algebraMap ℤ _) z) ≠ 0 := by
    rw [ϖ_eval₂]; exact hz hP
  have hpres : ((P.eval₂ (algebraMap ℤ FQ) g : FQ) : LaurentSeries ℚ) * ιK ℚ 1
      = ιK ℚ (P.eval₂ (algebraMap ℤ _) z) := by rw [map_one, mul_one, hcoe]
  have h1 : ϖ p 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  refine ⟨⟨_, 1, h1, hpres⟩, ?_⟩
  change IsGaussZ p (((P.eval₂ (algebraMap ℤ FQ) g)⁻¹ : FQ) : LaurentSeries ℚ)
  rw [IntermediateField.coe_inv]
  exact IsGaussZ.inv_of hred hpres h1

variable (N p)

theorem atkinLehner_swap (hpN : ¬ p ∣ N) :
    atkinLehnerInvolutionFull N p (jFQ N p) = jpFQ N p ∧
      atkinLehnerInvolutionFull N p (jpFQ N p) = jFQ N p := by
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  obtain ⟨h1, h2⟩ := hσ 1 inferInstance (one_dvd N)
  have hjF : jFQ N p = ⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ :=
    Subtype.ext (by change jq = qExpand ℚ 1 jq; rw [qExpand_one_apply])
  have hjpF : jpFQ N p = ⟨qExpand ℚ (1 * p) jq, jqd_mem_full (N * p) (Nat.mul_dvd_mul_right (one_dvd N) p)⟩ :=
    Subtype.ext (by change qExpand ℚ p jq = qExpand ℚ (1 * p) jq; rw [qExpand_congr (one_mul p)])
  rw [hjF, hjpF]
  exact ⟨h1, h2⟩

def gaussZ' : ValuationSubring FQ :=
  (gaussZ p (N * p)).comap ((atkinLehnerInvolutionFull N p : FQ ≃ₐ[ℚ] FQ) : FQ →+* FQ)

theorem mem_gaussZ'_iff (f : FQ) : f ∈ gaussZ' N p ↔ atkinLehnerInvolutionFull N p f ∈ gaussZ p (N * p) :=
  Iff.rfl

variable {N p}

theorem mem_nonunits_gaussZ'_iff (f : FQ) :
    f ∈ (gaussZ' N p).nonunits ↔ atkinLehnerInvolutionFull N p f ∈ (gaussZ p (N * p)).nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', mem_gaussZ'_iff, mem_gaussZ'_iff, map_inv₀,
    EmbeddingLike.map_eq_zero_iff]

end Generators

section Pair

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "FQ" => (↥(modularFunctionFieldFull (N * p)) : Type)
local notation "W₀" => gaussZ p (N * p)
local notation "W₁" => gaussZ' N p
local notation "w" => atkinLehnerInvolutionFull N p

theorem gaussZ_ne_gaussZ' (hpN : ¬ p ∣ N) : (W₀ : ValuationSubring FQ) ≠ W₁ := by
  obtain ⟨hw₁, hw₂⟩ := atkinLehner_swap N p hpN
  have hjZ : ϖ p (jqModC ℤ) ≠ 0 := by rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial _
  have hjpZ : ϖ p (qExpand ℤ p (jqModC ℤ)) ≠ 0 := by
    rw [coeffMap_qExpand, coeffMap_jqModC]
    exact fun h => jqModC_ne_zero_of_nontrivial (ZMod p)
      (qExpand_injective (R := ZMod p) (N := p) (by rw [h, map_zero]))
  have hj0 : (jFQ N p : FQ) ≠ 0 := by
    intro h0
    have := congrArg (fun z : FQ => (z : LaurentSeries ℚ)) h0
    simp only [coe_jFQ, ZeroMemClass.coe_zero, ιK_eq_zero_iff] at this
    exact hjZ (by rw [this, map_zero])
  have hjp0 : (jpFQ N p : FQ) ≠ 0 := by
    intro h0
    have := congrArg (fun z : FQ => (z : LaurentSeries ℚ)) h0
    simp only [coe_jpFQ, ZeroMemClass.coe_zero, ιK_eq_zero_iff] at this
    exact hjpZ (by rw [this, map_zero])

  set h : FQ := jpFQ N p / (jFQ N p) ^ p - 1 with hh
  set x : LaurentSeries ℤ := qExpand ℤ p (jqModC ℤ) - (jqModC ℤ) ^ p with hx
  set y : LaurentSeries ℤ := (jqModC ℤ) ^ p with hy
  have hyred : ϖ p y ≠ 0 := by rw [hy, map_pow]; exact pow_ne_zero _ hjZ
  have hxred : ϖ p x = 0 := by
    rw [hx, map_sub, map_pow, coeffMap_qExpand, coeffMap_jqModC,
      qExpand_jqModC_eq_pow_unconditional (ZMod p), sub_self]
  have hpres : (h : LaurentSeries ℚ) * ιK ℚ y = ιK ℚ x := by
    have hjy : ιK ℚ y ≠ 0 := ιK_ne_zero_of_ϖ hyred
    rw [hh, AddSubgroupClass.coe_sub, IntermediateField.coe_div, IntermediateField.coe_pow, coe_jpFQ,
      coe_jFQ, IntermediateField.coe_one, ← map_pow, hx, map_sub, map_pow, sub_mul,
      div_mul_cancel₀ _ (by rw [map_pow] at hjy; exact hjy), one_mul]
  have hmem : h ∈ (W₀ : ValuationSubring FQ) := ⟨x, y, hyred, hpres⟩

  have hnon : h ∈ (W₀ : ValuationSubring FQ).nonunits := by
    rw [mem_nonunits_iff']
    refine ⟨hmem, ?_⟩
    by_cases hh0 : h = 0
    · exact Or.inl hh0
    · right
      intro hinv
      have hh0' : (h : LaurentSeries ℚ) ≠ 0 := fun e => hh0 (Subtype.ext e)
      have := IsGaussZ.ϖ_ne_zero_of_inv hh0' hyred hpres (by
        have : IsGaussZ p ((h⁻¹ : FQ) : LaurentSeries ℚ) := hinv
        rwa [IntermediateField.coe_inv] at this)
      exact this hxred

  set x' : LaurentSeries ℤ := jqModC ℤ - (qExpand ℤ p (jqModC ℤ)) ^ p with hx'
  set y' : LaurentSeries ℤ := (qExpand ℤ p (jqModC ℤ)) ^ p with hy'
  have hy'red : ϖ p y' ≠ 0 := by rw [hy', map_pow]; exact pow_ne_zero _ hjpZ
  have hx'red : ϖ p x' ≠ 0 := by
    rw [hx', map_sub, map_pow, coeffMap_qExpand, coeffMap_jqModC,
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
  have hwh : w h = jFQ N p / (jpFQ N p) ^ p - 1 := by
    rw [hh, map_sub, map_one, map_div₀, map_pow, hw₁, hw₂]
  have hpres' : ((w h : FQ) : LaurentSeries ℚ) * ιK ℚ y' = ιK ℚ x' := by
    have hjy : ιK ℚ y' ≠ 0 := ιK_ne_zero_of_ϖ hy'red
    rw [hwh, AddSubgroupClass.coe_sub, IntermediateField.coe_div, IntermediateField.coe_pow, coe_jpFQ,
      coe_jFQ, IntermediateField.coe_one, ← map_pow, hx', map_sub, map_pow, sub_mul,
      div_mul_cancel₀ _ (by rw [hy', map_pow] at hjy; exact hjy), one_mul]
  have hunit : (w h)⁻¹ ∈ (W₀ : ValuationSubring FQ) := by
    change IsGaussZ p (((w h)⁻¹ : FQ) : LaurentSeries ℚ)
    rw [IntermediateField.coe_inv]
    exact IsGaussZ.inv_of hx'red hpres' hy'red

  intro heq
  have h1 : h⁻¹ ∈ (W₁ : ValuationSubring FQ) := by
    rw [mem_gaussZ'_iff, map_inv₀]; exact hunit
  rw [← heq] at h1
  rw [mem_nonunits_iff'] at hnon
  rcases hnon.2 with h0 | hninv
  ·
    have : ((w h : FQ) : LaurentSeries ℚ) = 0 := by rw [h0, map_zero]; rfl
    rw [this, zero_mul] at hpres'
    exact ιK_ne_zero_of_ϖ hx'red hpres'.symm
  · exact hninv h1

theorem props_gaussZ :
    ((p : ℕ) : FQ) ∈ (W₀ : ValuationSubring FQ).nonunits ∧
    (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      P.eval₂ (algebraMap ℤ FQ) (jFQ N p) ∈ (W₀ : ValuationSubring FQ) ∧
        (P.eval₂ (algebraMap ℤ FQ) (jFQ N p))⁻¹ ∈ (W₀ : ValuationSubring FQ)) ∧
    (∀ f ∈ (W₀ : ValuationSubring FQ).nonunits, f * ((p : ℕ) : FQ)⁻¹ ∈ (W₀ : ValuationSubring FQ)) := by
  refine ⟨p_mem_nonunits_gaussZ p (N * p), fun P hP => ?_, mul_inv_p_mem_gaussZ p (N * p)⟩
  refine eval₂_mem_and_inv_mem_gaussZ hP (jFQ N p) (jqModC ℤ) (coe_jFQ N p) (fun hQ => ?_)
  rw [coeffMap_jqModC]; exact eval₂_jqModC_ne_zero p hQ

theorem props_gaussZ' (hpN : ¬ p ∣ N) :
    ((p : ℕ) : FQ) ∈ (W₁ : ValuationSubring FQ).nonunits ∧
    (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      P.eval₂ (algebraMap ℤ FQ) (jFQ N p) ∈ (W₁ : ValuationSubring FQ) ∧
        (P.eval₂ (algebraMap ℤ FQ) (jFQ N p))⁻¹ ∈ (W₁ : ValuationSubring FQ)) ∧
    (∀ f ∈ (W₁ : ValuationSubring FQ).nonunits, f * ((p : ℕ) : FQ)⁻¹ ∈ (W₁ : ValuationSubring FQ)) := by
  obtain ⟨hw₁, hw₂⟩ := atkinLehner_swap N p hpN
  refine ⟨?_, fun P hP => ?_, fun f hf => ?_⟩
  · rw [mem_nonunits_gaussZ'_iff, map_natCast]; exact p_mem_nonunits_gaussZ p (N * p)
  · have hev : w (P.eval₂ (algebraMap ℤ FQ) (jFQ N p)) = P.eval₂ (algebraMap ℤ FQ) (jpFQ N p) := by
      have h1 := Polynomial.hom_eval₂ P (algebraMap ℤ FQ) ((w : FQ ≃ₐ[ℚ] FQ) : FQ →+* FQ) (jFQ N p)
      change ((w : FQ ≃ₐ[ℚ] FQ) : FQ →+* FQ) (P.eval₂ (algebraMap ℤ FQ) (jFQ N p)) = _
      rw [h1]
      change P.eval₂ _ (w (jFQ N p)) = _
      rw [hw₁]
      congr 1
      exact RingHom.ext_int _ _
    rw [mem_gaussZ'_iff, mem_gaussZ'_iff, map_inv₀, hev]
    refine eval₂_mem_and_inv_mem_gaussZ hP (jpFQ N p) _ (coe_jpFQ N p) (fun hQ => ?_)
    rw [coeffMap_qExpand, coeffMap_jqModC]; exact eval₂_qExpand_jqModC_ne_zero p hQ
  · rw [mem_nonunits_gaussZ'_iff] at hf
    rw [mem_gaussZ'_iff, map_mul, map_inv₀, map_natCast]
    exact mul_inv_p_mem_gaussZ p (N * p) _ hf

end Pair

section General

theorem exists_valuationSubring_comap_eq {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring K) : ∃ B : ValuationSubring L, ∀ f : K, f ∈ V ↔ φ f ∈ B := by
  let Lc : LocalSubring L := V.toLocalSubring.map φ
  obtain ⟨B, hB⟩ := Lc.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hB
  have hmapmem : ∀ f : K, f ∈ V → φ f ∈ Lc.toSubring := fun f hf => ⟨f, hf, rfl⟩
  refine ⟨B, fun f => ⟨fun hf => hle (hmapmem f hf), fun hfB => ?_⟩⟩
  by_contra hfV
  have hf0 : f ≠ 0 := by rintro rfl; exact hfV V.zero_mem
  have hinv : f⁻¹ ∈ V := (V.mem_or_inv_mem f).resolve_left hfV

  have hnu : ¬ IsUnit (⟨φ f⁻¹, hmapmem _ hinv⟩ : Lc.toSubring) := by
    rintro ⟨u, hu⟩
    obtain ⟨g, hg, hgeq⟩ : ((↑u⁻¹ : Lc.toSubring) : L) ∈ Lc.toSubring := SetLike.coe_mem _
    have hmul : ((↑u⁻¹ : Lc.toSubring) : L) * φ f⁻¹ = 1 := by
      have := congrArg (fun y : Lc.toSubring => (y : L)) u.inv_mul
      simpa [hu] using this
    rw [← hgeq, ← map_mul, ← map_one φ] at hmul
    have hgf : g * f⁻¹ = 1 := φ.injective hmul
    have hgf' : g = f := by
      have := congrArg (· * f) hgf
      simpa [mul_assoc, inv_mul_cancel₀ hf0] using this
    exact hfV (hgf' ▸ hg)

  have hnuB : ¬ IsUnit (Subring.inclusion hle ⟨φ f⁻¹, hmapmem _ hinv⟩) :=
    fun h => hnu (hloc.map_nonunit _ h)
  apply hnuB
  have hφf0 : φ f ≠ 0 := (map_ne_zero φ).mpr hf0
  refine ⟨⟨⟨φ f⁻¹, hle (hmapmem _ hinv)⟩, ⟨φ f, hfB⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · change φ f⁻¹ * φ f = 1; rw [map_inv₀, inv_mul_cancel₀ hφf0]
  · change φ f * φ f⁻¹ = 1; rw [map_inv₀, mul_inv_cancel₀ hφf0]

theorem exists_primitive_scaling {L : Type*} [Field L] (A : ValuationSubring L) {r : Polynomial L}
    (hr : r ≠ 0) : ∃ (c : L) (r₀ : Polynomial A), c ≠ 0 ∧ r = C c * r₀.map (algebraMap A L) ∧
      ∃ i, IsUnit (r₀.coeff i) := by
  have hne : r.support.Nonempty := Polynomial.nonempty_support_iff.mpr hr
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image r.support (fun i => A.valuation (r.coeff i)) hne
  set c := r.coeff i₀ with hc
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  have hcoef : ∀ i, c⁻¹ * r.coeff i ∈ A := by
    intro i
    by_cases hi : i ∈ r.support
    · rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      have h1 := hmax i hi
      have hvc : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
      calc (A.valuation c)⁻¹ * A.valuation (r.coeff i)
          ≤ (A.valuation c)⁻¹ * A.valuation c := by gcongr
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]; exact A.zero_mem
  have hlifts : C c⁻¹ * r ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    exact ⟨⟨_, hcoef n⟩, rfl⟩
  obtain ⟨r₀, hr₀⟩ := (Polynomial.mem_lifts _).mp hlifts
  refine ⟨c, r₀, hc0, ?_, i₀, ?_⟩
  · rw [hr₀, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
  · have h1 : algebraMap A L (r₀.coeff i₀) = 1 := by
      have := congrArg (fun q : Polynomial L => q.coeff i₀) hr₀
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
      rw [this, ← hc, inv_mul_cancel₀ hc0]
    have h2 : r₀.coeff i₀ = 1 := by
      apply Subtype.ext
      exact h1
    rw [h2]; exact isUnit_one

theorem eval₂_coe_eq {L E : Type*} [Field L] [Field E] (A : ValuationSubring L)
    (W : ValuationSubring E) (ρ : A →+* W) (θ : L →+* E)
    (hρ : ∀ a : A, ((ρ a : W) : E) = θ (a : L)) (x : W) (P : Polynomial A) :
    ((P.eval₂ ρ x : W) : E) = P.eval₂ (θ.comp (algebraMap A L)) (x : E) := by
  have h := Polynomial.hom_eval₂ P ρ (W.subtype) x
  change W.subtype (P.eval₂ ρ x) = _
  rw [h]
  congr 1
  exact RingHom.ext fun a => hρ a

end General

section GaussOnJ

variable {L E : Type*} [Field L] [Field E] [Algebra L E]

def IsGaussOn (A : ValuationSubring L) (W : ValuationSubring E) (x : E) : Prop :=
  (∀ c : L, algebraMap L E c ∈ W ↔ c ∈ A) ∧ x ∈ W ∧
    ∀ P : Polynomial A, (∃ i, IsUnit (P.coeff i)) →
      P.eval₂ ((algebraMap L E).comp (algebraMap A L)) x ∈ W ∧
        (P.eval₂ ((algebraMap L E).comp (algebraMap A L)) x)⁻¹ ∈ W

theorem IsGaussOn.mem_iff_mem {A : ValuationSubring L} {W W' : ValuationSubring E} {x : E}
    (hW : IsGaussOn A W x) (hW' : IsGaussOn A W' x) :
    ∀ e ∈ IntermediateField.adjoin L ({x} : Set E), e ∈ W ↔ e ∈ W' := by
  intro e he
  rw [IntermediateField.mem_adjoin_simple_iff] at he
  obtain ⟨r, s, rfl⟩ := he

  by_cases hs0 : aeval x s = 0
  · rw [hs0, div_zero]; exact ⟨fun _ => W'.zero_mem, fun _ => W.zero_mem⟩
  by_cases hr0 : r = 0
  · rw [hr0, map_zero, zero_div]; exact ⟨fun _ => W'.zero_mem, fun _ => W.zero_mem⟩
  have hs : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
  obtain ⟨c, r₀, hc, hr, i, hi⟩ := exists_primitive_scaling A hr0
  obtain ⟨c', s₀, hc', hs', i', hi'⟩ := exists_primitive_scaling A hs

  set u : E := r₀.eval₂ ((algebraMap L E).comp (algebraMap A L)) x with hu
  set v : E := s₀.eval₂ ((algebraMap L E).comp (algebraMap A L)) x with hv
  have hru : aeval x r = algebraMap L E c * u := by
    rw [hr, map_mul, Polynomial.aeval_C, Polynomial.aeval_def, Polynomial.eval₂_map]
  have hsv : aeval x s = algebraMap L E c' * v := by
    rw [hs', map_mul, Polynomial.aeval_C, Polynomial.aeval_def, Polynomial.eval₂_map]
  have hv0 : v ≠ 0 := by
    intro h0; apply hs0; rw [hsv, h0, mul_zero]
  obtain ⟨huW, huW'⟩ := (hW.2.2 r₀ ⟨i, hi⟩)
  obtain ⟨hvW, hvW'⟩ := (hW.2.2 s₀ ⟨i', hi'⟩)
  obtain ⟨huV, huV'⟩ := (hW'.2.2 r₀ ⟨i, hi⟩)
  obtain ⟨hvV, hvV'⟩ := (hW'.2.2 s₀ ⟨i', hi'⟩)

  by_cases hu0 : u = 0
  · have : aeval x r / aeval x s = 0 := by rw [hru, hu0, mul_zero, zero_div]
    rw [this]; exact ⟨fun _ => W'.zero_mem, fun _ => W.zero_mem⟩

  have hkey : aeval x r / aeval x s = algebraMap L E (c / c') * (u * v⁻¹) := by
    rw [hru, hsv, map_div₀]
    have hc'0 : algebraMap L E c' ≠ 0 := (_root_.map_ne_zero _).mpr hc'
    field_simp
  have hcrit : ∀ (X : ValuationSubring E), (∀ c : L, algebraMap L E c ∈ X ↔ c ∈ A) →
      u ∈ X → u⁻¹ ∈ X → v ∈ X → v⁻¹ ∈ X →
      (aeval x r / aeval x s ∈ X ↔ c / c' ∈ A) := by
    intro X hX huX huX' hvX hvX'
    rw [hkey, ← hX]
    constructor
    · intro h
      have : algebraMap L E (c / c') = algebraMap L E (c / c') * (u * v⁻¹) * (v * u⁻¹) := by
        field_simp
      rw [this]
      exact mul_mem h (mul_mem hvX huX')
    · intro h
      exact mul_mem h (mul_mem huX hvX')
  rw [hcrit W hW.1 huW huW' hvW hvW', hcrit W' hW'.1 huV huV' hvV hvV']

end GaussOnJ

section Descent

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "FQ" => (↥(modularFunctionFieldFull (N * p)) : Type)
local notation "ℚ̄" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => (↥(modularFunctionFieldBar (N * p)) : Type)
local notation "W₀" => gaussZ p (N * p)
local notation "W₁" => gaussZ' N p
local notation "w" => atkinLehnerInvolutionFull N p

def emb : FQ →+* FF where
  toFun f := ⟨coeffEmb ℚ̄ (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚ̄ f.2⟩
  map_one' := Subtype.ext (by change coeffEmb ℚ̄ ((1 : FQ) : LaurentSeries ℚ) = 1; simp)
  map_mul' f g := Subtype.ext (by
    change coeffEmb ℚ̄ ((f * g : FQ) : LaurentSeries ℚ) = coeffEmb ℚ̄ (f : LaurentSeries ℚ) * coeffEmb ℚ̄ (g : LaurentSeries ℚ)
    rw [IntermediateField.coe_mul, map_mul])
  map_zero' := Subtype.ext (by change coeffEmb ℚ̄ ((0 : FQ) : LaurentSeries ℚ) = 0; simp)
  map_add' f g := Subtype.ext (by
    change coeffEmb ℚ̄ ((f + g : FQ) : LaurentSeries ℚ) = coeffEmb ℚ̄ (f : LaurentSeries ℚ) + coeffEmb ℚ̄ (g : LaurentSeries ℚ)
    rw [IntermediateField.coe_add, map_add])

@[scoped simp] theorem coe_emb (f : FQ) : ((emb N p f : FF) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ (f : LaurentSeries ℚ) := rfl

def jFF : FF := ⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄
  (modularFunctionField_le_full (N * p) (jq_mem (N * p)))⟩

theorem emb_jFQ : emb N p (jFQ N p) = jFF N p := Subtype.ext rfl

theorem geomAut_emb (f : FQ) :
    geomAut ℚ̄ (modularFunctionFieldFull (N * p)) w (emb N p f) = emb N p (w f) :=
  geomAut_coeffEmb ℚ̄ (modularFunctionFieldFull (N * p)) w f

theorem emb_natCast : emb N p ((p : ℕ) : FQ) = ((p : ℕ) : FF) := map_natCast _ p

theorem coeffEmb_ιK (x : LaurentSeries ℤ) : coeffEmb ℚ̄ (ιK ℚ x) = ιK ℚ̄ x := by
  change coeffMap (algebraMap ℚ ℚ̄) (coeffMap (Int.castRingHom ℚ) x) = _
  rw [coeffMap_coeffMap]
  exact congrArg (fun g : ℤ →+* ℚ̄ => coeffMap g x) (RingHom.ext_int _ _)

variable {N p}
variable {A : ValuationSubring (AlgebraicClosure ℚ)}

abbrev toA (A : ValuationSubring (AlgebraicClosure ℚ)) : LaurentSeries ℤ →+* LaurentSeries A :=
  coeffMap (Int.castRingHom A)

theorem ι_toA (x : LaurentSeries ℤ) : coeffMap A.subtype (toA A x) = ιK ℚ̄ x := by
  rw [coeffMap_coeffMap]
  exact congrArg (fun g : ℤ →+* ℚ̄ => coeffMap g x) (RingHom.ext_int _ _)

theorem ϖA_toA_ne_zero (hA : A.LiesOverPrime p) {y : LaurentSeries ℤ} (hy : ϖ p y ≠ 0) :
    coeffMap (IsLocalRing.residue A) (toA A y) ≠ 0 := by

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    have hℓ : ((p : A) : ℚ̄) ∈ A.nonunits := by simpa [ValuationSubring.LiesOverPrime] using hA
    rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]; exact hℓ
  haveI : CharP (IsLocalRing.ResidueField A) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpk
  let θ : ZMod p →+* IsLocalRing.ResidueField A := ZMod.castHom (dvd_refl p) _
  have hθ : (IsLocalRing.residue A).comp (Int.castRingHom A) = θ.comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [coeffMap_coeffMap, hθ, ← coeffMap_coeffMap]
  intro h0
  apply hy
  ext n
  have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h0
  simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
  rw [HahnSeries.coeff_zero]
  exact (map_eq_zero_iff θ θ.injective).mp h1

theorem mem_and_inv_mem_of_primitive (R₀ : ValuationSubring FF)
    (hmem : ∀ g : FF, g ∈ R₀ ↔ ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (g : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hA : A.LiesOverPrime p) {z : LaurentSeries ℤ} (hz : ϖ p z ≠ 0) (u : FF)
    (hu : (u : LaurentSeries ℚ̄) = ιK ℚ̄ z) : u ∈ R₀ ∧ u⁻¹ ∈ R₀ := by
  have hzA := ϖA_toA_ne_zero hA hz
  have h1 : coeffMap (IsLocalRing.residue A) (1 : LaurentSeries A) ≠ 0 := by
    rw [map_one]; exact one_ne_zero
  have hu0 : (u : LaurentSeries ℚ̄) ≠ 0 := by
    rw [hu, ← ι_toA]
    intro h0
    apply hzA
    have : toA A z = 0 := by
      have hinj : Function.Injective (coeffMap A.subtype : LaurentSeries A → LaurentSeries ℚ̄) := by
        intro x y hxy; ext n
        have := congrArg (fun s : LaurentSeries ℚ̄ => s.coeff n) hxy
        simp only [coeffMap_coeff] at this
        exact this
      exact hinj (by rw [h0, map_zero])
    rw [this, map_zero]
  refine ⟨(hmem u).mpr ⟨toA A z, 1, h1, by rw [map_one, mul_one, ι_toA, hu]⟩,
    (hmem u⁻¹).mpr ⟨1, toA A z, hzA, ?_⟩⟩
  rw [IntermediateField.coe_inv, ι_toA, ← hu, map_one, inv_mul_cancel₀ hu0]

theorem emb_mem_gauss_iff (hA : A.LiesOverPrime p)
    (R₀ : ValuationSubring FF)
    (hRA : ∀ c : ℚ̄, algebraMap ℚ̄ FF c ∈ R₀ ↔ c ∈ A)
    (hmem : ∀ g : FF, g ∈ R₀ ↔ ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (g : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x)
    (f : FQ) : emb N p f ∈ R₀ ↔ f ∈ (W₀ : ValuationSubring FQ) := by
  constructor
  · intro hf
    by_cases hf0 : f = 0
    · rw [hf0]; exact zero_mem _
    obtain ⟨a, b, P₀, Q₀, hP₀, hQ₀, hPF, hQF, h⟩ := exists_pFrac (p := p) hf0
    rcases le_or_gt b a with hab | hab
    · exact isGaussZ_of_pFrac hQ₀ h hab

    exfalso
    have hp0Q : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

    set uP : FQ := ⟨ιK ℚ P₀, hPF⟩ with huP
    set uQ : FQ := ⟨ιK ℚ Q₀, hQF⟩ with huQ

    have hrel : f * uQ * ((p : ℕ) : FQ) ^ b = ((p : ℕ) : FQ) ^ a * uP := by
      apply Subtype.ext
      change (f : LaurentSeries ℚ) * ιK ℚ Q₀ * (((p : ℕ) : FQ) ^ b : FQ) = ((((p : ℕ) : FQ) ^ a : FQ) : LaurentSeries ℚ) * ιK ℚ P₀
      have hc : ∀ n : ℕ, ((((p : ℕ) : FQ) ^ n : FQ) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) ((p : ℚ) ^ n) := by
        intro n; rw [IntermediateField.coe_pow, map_pow]; push_cast; rfl
      rw [hc, hc, h]

    have hrel' : emb N p f * emb N p uQ * ((p : ℕ) : FF) ^ b = ((p : ℕ) : FF) ^ a * emb N p uP := by
      have := congrArg (emb N p) hrel
      simpa [map_mul, map_pow, map_natCast] using this
    obtain ⟨huPm, huPi⟩ := mem_and_inv_mem_of_primitive R₀ hmem hA hP₀ (emb N p uP)
      (by rw [coe_emb, huP]; exact coeffEmb_ιK P₀)
    obtain ⟨huQm, -⟩ := mem_and_inv_mem_of_primitive R₀ hmem hA hQ₀ (emb N p uQ)
      (by rw [coe_emb, huQ]; exact coeffEmb_ιK Q₀)

    have hpA : ((p : ℕ) : ℚ̄) ∈ A.nonunits := hA
    rw [mem_nonunits_iff'] at hpA
    obtain ⟨hpmem, hpnu⟩ := hpA
    have hp0 : ((p : ℕ) : ℚ̄) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hpinv : ((p : ℕ) : ℚ̄)⁻¹ ∉ A := hpnu.resolve_left hp0
    apply hpinv
    rw [← hRA]

    have hpR : ((p : ℕ) : FF) ∈ R₀ := by
      have := (hRA (p : ℕ)).mpr hpmem
      rwa [map_natCast] at this
    have hpF0 : ((p : ℕ) : FF) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

    have huP0 : emb N p uP ≠ 0 := by
      intro h0
      have := congrArg (fun g : FF => (g : LaurentSeries ℚ̄)) h0
      rw [coe_emb, huP, ZeroMemClass.coe_zero, coeffEmb_ιK, ← ι_toA] at this
      apply ϖA_toA_ne_zero hA hP₀
      have hinj : Function.Injective (coeffMap A.subtype : LaurentSeries A → LaurentSeries ℚ̄) := by
        intro x y hxy; ext n
        have := congrArg (fun s : LaurentSeries ℚ̄ => s.coeff n) hxy
        simp only [coeffMap_coeff] at this
        exact this
      rw [hinj (this.trans (map_zero _).symm), map_zero]
    have hpa0 : ((p : ℕ) : FF) ^ a ≠ 0 := pow_ne_zero _ hpF0
    have hE : ((p : ℕ) : FF) ^ (b - a) * (emb N p f * emb N p uQ) = emb N p uP := by
      apply mul_right_cancel₀ hpa0
      calc ((p : ℕ) : FF) ^ (b - a) * (emb N p f * emb N p uQ) * ((p : ℕ) : FF) ^ a
          = emb N p f * emb N p uQ * ((p : ℕ) : FF) ^ b := by
            rw [mul_comm (((p : ℕ) : FF) ^ (b - a)), mul_assoc, pow_sub_mul_pow _ hab.le]
        _ = ((p : ℕ) : FF) ^ a * emb N p uP := hrel'
        _ = emb N p uP * ((p : ℕ) : FF) ^ a := mul_comm _ _
    have hba' : b - a = (b - a - 1) + 1 := by omega
    rw [hba', pow_succ] at hE
    have h3 : ((p : ℕ) : FF) ^ (b - a - 1) * (emb N p f * emb N p uQ) = ((p : ℕ) : FF)⁻¹ * emb N p uP := by
      rw [eq_inv_mul_iff_mul_eq₀ hpF0, ← hE]; ring
    have hkey : (algebraMap ℚ̄ FF) (((p : ℕ) : ℚ̄)⁻¹) =
        ((p : ℕ) : FF) ^ (b - a - 1) * (emb N p f * emb N p uQ * (emb N p uP)⁻¹) := by
      rw [map_inv₀, map_natCast, ← mul_assoc, h3, mul_assoc, mul_inv_cancel₀ huP0, mul_one]
    rw [hkey]
    exact mul_mem (pow_mem hpR _) (mul_mem (mul_mem hf huQm) huPi)
  · rintro ⟨x, y, hy, h⟩
    rw [hmem]
    refine ⟨toA A x, toA A y, ϖA_toA_ne_zero hA hy, ?_⟩
    rw [ι_toA, ι_toA, coe_emb, ← coeffEmb_ιK, ← coeffEmb_ιK, ← map_mul, h]

def constHom (W : ValuationSubring FF) (hW : ∀ c : ℚ̄, algebraMap ℚ̄ FF c ∈ W ↔ c ∈ A) :
    A →+* W where
  toFun a := ⟨algebraMap ℚ̄ FF a, (hW a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (W : ValuationSubring FF) (hW : ∀ c : ℚ̄, algebraMap ℚ̄ FF c ∈ W ↔ c ∈ A)
    (a : A) : ((constHom W hW a : W) : FF) = algebraMap ℚ̄ FF a := rfl

set_option maxHeartbeats 6400000 in

theorem isGaussOn_regularProlongation
    (R₀ : RegularProlongation A FF (↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)))
    (hj₀ : jFF N p ∈ R₀.integers)
    (hresj : ((R₀.residue ⟨_, hj₀⟩ : ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
      LaurentSeries (IsLocalRing.ResidueField A)) = jqModC (IsLocalRing.ResidueField A)) :
    IsGaussOn A R₀.integers (jFF N p) := by
  refine ⟨R₀.algebraMap_mem_iff, hj₀, fun P ⟨i, hi⟩ => ?_⟩
  set kk := IsLocalRing.ResidueField A
  set Fb := (↥(modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
  let ρ : A →+* R₀.integers := constHom R₀.integers R₀.algebraMap_mem_iff
  set e : R₀.integers := P.eval₂ ρ ⟨jFF N p, hj₀⟩ with he
  have hcoe : (e : FF) = P.eval₂ ((algebraMap ℚ̄ FF).comp (algebraMap A ℚ̄)) (jFF N p) :=
    eval₂_coe_eq A R₀.integers ρ (algebraMap ℚ̄ FF) (fun a => rfl) ⟨jFF N p, hj₀⟩ P

  have hρres : R₀.residue.comp ρ = (algebraMap kk Fb).comp (IsLocalRing.residue A) := by
    refine RingHom.ext fun a => ?_
    exact R₀.residue_algebraMap a
  have hres : R₀.residue e = (P.map (IsLocalRing.residue A)).eval₂ (algebraMap kk Fb)
      (R₀.residue ⟨jFF N p, hj₀⟩) := by
    rw [he, Polynomial.hom_eval₂, hρres, Polynomial.eval₂_map]
  have hPbar : P.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    have := congrArg (fun q => Polynomial.coeff q i) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
    exact (hi.map (IsLocalRing.residue A)).ne_zero this
  have htr : Transcendental kk (R₀.residue ⟨jFF N p, hj₀⟩) := by
    intro halg
    have h1 : IsAlgebraic kk (((modularFunctionFieldFullC kk N).val) (R₀.residue ⟨jFF N p, hj₀⟩)) :=
      (isAlgebraic_algHom_iff (modularFunctionFieldFullC kk N).val Subtype.val_injective).mpr halg
    change IsAlgebraic kk ((R₀.residue ⟨jFF N p, hj₀⟩ : Fb) : LaurentSeries kk) at h1
    rw [hresj] at h1
    exact ModularCurve.transcendental_jqModC kk h1
  have hres_ne : R₀.residue e ≠ 0 := by
    rw [hres]
    intro h0
    exact htr ⟨_, hPbar, by rw [Polynomial.aeval_def]; exact h0⟩
  obtain ⟨u, hu⟩ := R₀.isUnit_of_residue_ne_zero hres_ne
  have he0 : (e : FF) ≠ 0 := by
    intro h0
    apply hres_ne
    have : e = 0 := Subtype.ext h0
    rw [this, map_zero]
  refine ⟨by rw [← hcoe]; exact e.2, ?_⟩
  rw [← hcoe]
  exact (isUnit_iff_inv_mem R₀.integers e.2 he0).mp (by
    have : (⟨(e : FF), e.2⟩ : R₀.integers) = e := Subtype.ext rfl
    rw [this]; exact ⟨u, hu⟩)

theorem emb_mem_nonunits {V : ValuationSubring FQ} {Vt : ValuationSubring FF}
    (hVt : ∀ f : FQ, f ∈ V ↔ emb N p f ∈ Vt) {f : FQ} (hf : f ∈ V.nonunits) :
    emb N p f ∈ Vt.nonunits := by
  rw [mem_nonunits_iff'] at hf ⊢
  refine ⟨(hVt f).mp hf.1, ?_⟩
  rcases hf.2 with h0 | hinv
  · left; rw [h0, map_zero]
  · right; rw [← map_inv₀, ← hVt]; exact hinv

set_option maxHeartbeats 12800000 in

theorem liesOverPrime_and_isGaussOn_extension {V : ValuationSubring FQ}
    (hpV : ((p : ℕ) : FQ) ∈ V.nonunits)
    (hjV : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      P.eval₂ (algebraMap ℤ FQ) (jFQ N p) ∈ V ∧ (P.eval₂ (algebraMap ℤ FQ) (jFQ N p))⁻¹ ∈ V)
    {Vt : ValuationSubring FF} (hVt : ∀ f : FQ, f ∈ V ↔ emb N p f ∈ Vt) :
    (Vt.comap (algebraMap ℚ̄ FF)).LiesOverPrime p ∧
      IsGaussOn (Vt.comap (algebraMap ℚ̄ FF)) Vt (jFF N p) := by
  set A' : ValuationSubring ℚ̄ := Vt.comap (algebraMap ℚ̄ FF) with hA'
  have hmemA : ∀ c : ℚ̄, c ∈ A' ↔ algebraMap ℚ̄ FF c ∈ Vt := fun c => ValuationSubring.mem_comap

  have hpVt : ((p : ℕ) : FF) ∈ Vt.nonunits := by
    have := emb_mem_nonunits hVt hpV
    rwa [emb_natCast] at this
  have hp0 : ((p : ℕ) : ℚ̄) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hA'p : A'.LiesOverPrime p := by
    change ((p : ℕ) : ℚ̄) ∈ A'.nonunits
    rw [mem_nonunits_iff']
    rw [mem_nonunits_iff'] at hpVt
    refine ⟨(hmemA _).mpr (by rw [map_natCast]; exact hpVt.1), Or.inr fun hinv => ?_⟩
    rcases hpVt.2 with h0 | h0
    · exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h0
    · exact h0 (by rw [← map_natCast (algebraMap ℚ̄ FF), ← map_inv₀]; exact (hmemA _).mp hinv)
  refine ⟨hA'p, fun c => (hmemA c).symm, ?_, fun P ⟨i₀, hi₀⟩ => ?_⟩
  ·
    have hX := (hjV Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rw [Polynomial.eval₂_X] at hX
    rw [← emb_jFQ]; exact (hVt _).mp hX

  have hjVt : jFF N p ∈ Vt := by
    have hX := (hjV Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rw [Polynomial.eval₂_X] at hX
    rw [← emb_jFQ]; exact (hVt _).mp hX
  let ρ : A' →+* Vt := constHom Vt (fun c => (hmemA c).symm)
  set e : Vt := P.eval₂ ρ ⟨jFF N p, hjVt⟩ with he
  have hcoe : (e : FF) = P.eval₂ ((algebraMap ℚ̄ FF).comp (algebraMap A' ℚ̄)) (jFF N p) :=
    eval₂_coe_eq A' Vt ρ (algebraMap ℚ̄ FF) (fun a => rfl) ⟨jFF N p, hjVt⟩ P

  set κ := IsLocalRing.ResidueField Vt
  set π : Vt →+* κ := IsLocalRing.residue Vt
  have hπp : ((p : ℕ) : κ) = 0 := by
    have h1 : (((p : ℕ) : Vt) : FF) ∈ Vt.nonunits := by push_cast; exact hpVt
    rw [ValuationSubring.coe_mem_nonunits_iff] at h1
    rw [← map_natCast π, IsLocalRing.residue_eq_zero_iff]; exact h1
  haveI hchar : CharP κ p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hπp
  letI : Algebra (ZMod p) κ := (ZMod.castHom (dvd_refl p) κ).toAlgebra
  have hZ : (algebraMap (ZMod p) κ).comp (Int.castRingHom (ZMod p)) = algebraMap ℤ κ :=
    RingHom.ext_int _ _

  set jt : κ := π ⟨jFF N p, hjVt⟩ with hjt
  have hT : Transcendental (ZMod p) jt := by
    rintro ⟨Qb, hQb0, hQb⟩
    obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.intCast_surjective) Qb
    have hQred : Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by rw [hQ]; exact hQb0
    obtain ⟨hQV, hQV'⟩ := hjV Q hQred

    set eQ : Vt := Q.eval₂ (algebraMap ℤ Vt) ⟨jFF N p, hjVt⟩ with heQ
    have hcoeQ : (eQ : FF) = emb N p (Q.eval₂ (algebraMap ℤ FQ) (jFQ N p)) := by
      have h1 := Polynomial.hom_eval₂ Q (algebraMap ℤ Vt) Vt.subtype ⟨jFF N p, hjVt⟩
      have h2 := Polynomial.hom_eval₂ Q (algebraMap ℤ FQ) (emb N p) (jFQ N p)
      change Vt.subtype eQ = _
      rw [heQ, h1, h2, emb_jFQ]
      change Q.eval₂ _ (jFF N p) = Q.eval₂ _ (jFF N p)
      congr 1
      exact (RingHom.ext_int _ _)
    have hunit : IsUnit eQ := by
      have hmem' : (eQ : FF) ∈ Vt := eQ.2
      have hne : (eQ : FF) ≠ 0 := by
        rw [hcoeQ, _root_.map_ne_zero]
        intro h0
        rw [h0, inv_zero] at hQV'

        have := (props_gaussZ N p).2.1 Q hQred
        rw [h0, inv_zero] at this
        have hz : (0 : FQ) ∈ (W₀ : ValuationSubring FQ).nonunits := by
          rw [mem_nonunits_iff']; exact ⟨zero_mem _, Or.inl rfl⟩

        obtain ⟨x, y, hy, hxy⟩ := this.1
        exact absurd h0 (by
          intro h00
          have hQj := (props_gaussZ N p).2.1 Q hQred
          rw [h00] at hQj

          have hc := coe_eval₂ N p Q (jFQ N p) (jqModC ℤ) (coe_jFQ N p)
          rw [h00, ZeroMemClass.coe_zero] at hc
          have hz0 : Q.eval₂ (algebraMap ℤ (LaurentSeries ℤ)) (jqModC ℤ) = 0 :=
            (ιK_eq_zero_iff ℚ _).mp hc.symm
          have := ϖ_eval₂ p Q (jqModC ℤ)
          rw [hz0, map_zero, coeffMap_jqModC] at this
          exact eval₂_jqModC_ne_zero p hQred this.symm)
      exact (isUnit_iff_inv_mem Vt hmem' hne).mpr (by
        rw [hcoeQ, ← map_inv₀]; exact (hVt _).mp hQV') |> fun h => by
          have : (⟨(eQ : FF), hmem'⟩ : Vt) = eQ := Subtype.ext rfl
          rwa [this] at h
    have hπQ : π eQ ≠ 0 := by
      intro h0
      rw [IsLocalRing.residue_eq_zero_iff] at h0
      exact (IsLocalRing.mem_maximalIdeal _).mp h0 hunit
    apply hπQ
    have h3 : π eQ = (Q.map (Int.castRingHom (ZMod p))).eval₂ (algebraMap (ZMod p) κ) jt := by
      rw [heQ, Polynomial.hom_eval₂, Polynomial.eval₂_map, hZ, hjt]
      rfl
    rw [h3, hQ, ← Polynomial.aeval_def]; exact hQb

  have halgConst : ∀ a : A', IsAlgebraic (ZMod p) (π (ρ a)) := by
    intro a
    haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic (S := ℚ) (nonZeroDivisors ℤ)
    have halg : IsAlgebraic ℤ (a : ℚ̄) :=
      IsAlgebraic.restrictScalars ℤ ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (a : ℚ̄))
    obtain ⟨m, hm0, hma⟩ := halg
    set m₀ := m.primPart with hm₀
    have hm₀a : Polynomial.aeval (a : ℚ̄) m₀ = 0 := by
      have h1 : Polynomial.aeval (a : ℚ̄) m = algebraMap ℤ ℚ̄ m.content * Polynomial.aeval (a : ℚ̄) m₀ := by
        conv_lhs => rw [Polynomial.eq_C_content_mul_primPart m]
        rw [map_mul, Polynomial.aeval_C]
      rw [hma] at h1
      have hc : algebraMap ℤ ℚ̄ m.content ≠ 0 := by
        rw [Ne, eq_intCast, Int.cast_eq_zero, Polynomial.content_eq_zero_iff]; exact hm0
      exact (mul_eq_zero.mp h1.symm).resolve_left hc
    have hm₀red : m₀.map (Int.castRingHom (ZMod p)) ≠ 0 := by
      intro h0
      have hdvd : ∀ i, (p : ℤ) ∣ m₀.coeff i := by
        intro i
        have := congrArg (fun q => Polynomial.coeff q i) h0
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
      have hC : Polynomial.C (p : ℤ) ∣ m₀ := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd
      have hu := (Polynomial.isPrimitive_primPart m) (p : ℤ) hC
      rw [Int.isUnit_iff] at hu
      have hp2 := (Fact.out : p.Prime).two_le
      omega
    refine ⟨m₀.map (Int.castRingHom (ZMod p)), hm₀red, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hZ]
    have h1 : (m₀.eval₂ (algebraMap ℤ Vt) (ρ a) : Vt) = 0 := by
      apply Subtype.ext
      have h2 := Polynomial.hom_eval₂ m₀ (algebraMap ℤ Vt) Vt.subtype (ρ a)
      change Vt.subtype (m₀.eval₂ (algebraMap ℤ Vt) (ρ a)) = 0
      rw [h2]
      change m₀.eval₂ _ (algebraMap ℚ̄ FF (a : ℚ̄)) = 0
      have h3 := Polynomial.hom_eval₂ m₀ (algebraMap ℤ ℚ̄) (algebraMap ℚ̄ FF) (a : ℚ̄)
      rw [show Vt.subtype.comp (algebraMap ℤ Vt) = (algebraMap ℚ̄ FF).comp (algebraMap ℤ ℚ̄) from
        RingHom.ext_int _ _, ← h3, ← Polynomial.aeval_def, hm₀a, map_zero]
    have h4 := Polynomial.hom_eval₂ m₀ (algebraMap ℤ Vt) π (ρ a)
    rw [h1, map_zero] at h4
    rw [show algebraMap ℤ κ = π.comp (algebraMap ℤ Vt) from RingHom.ext_int _ _]
    exact h4.symm

  have hπe : π e ≠ 0 := by
    intro h0

    set Pt : Polynomial κ := P.map (π.comp ρ) with hPt
    have hPt0 : Pt ≠ 0 := by
      intro hz
      have := congrArg (fun q => Polynomial.coeff q i₀) hz
      simp only [hPt, Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.comp_apply] at this
      exact ((hi₀.map ρ).map π).ne_zero this
    have hPtj : Pt.eval jt = 0 := by
      have h1 := Polynomial.hom_eval₂ P ρ π ⟨jFF N p, hjVt⟩
      rw [← he, h0] at h1
      rw [hPt, Polynomial.eval_map, hjt]; exact h1.symm

    set S : Set κ := Set.range fun n : ℕ => Pt.coeff n with hS
    have hSalg : ∀ x ∈ S, IsIntegral (ZMod p) x := by
      rintro x ⟨n, rfl⟩
      dsimp only
      rw [hPt, Polynomial.coeff_map, RingHom.comp_apply]
      exact (halgConst (P.coeff n)).isIntegral
    haveI : Algebra.IsAlgebraic (ZMod p) (IntermediateField.adjoin (ZMod p) S) :=
      IntermediateField.isAlgebraic_adjoin hSalg
    set K₀ := IntermediateField.adjoin (ZMod p) S with hK₀
    have hlift : Pt ∈ Polynomial.lifts (algebraMap K₀ κ) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨Pt.coeff n, IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩⟩, rfl⟩
    obtain ⟨P₁, hP₁⟩ := (Polynomial.mem_lifts _).mp hlift
    have hP₁0 : P₁ ≠ 0 := by rintro rfl; rw [Polynomial.map_zero] at hP₁; exact hPt0 hP₁.symm
    have halgK₀ : IsAlgebraic K₀ jt := by
      refine ⟨P₁, hP₁0, ?_⟩
      rw [← Polynomial.aeval_map_algebraMap κ jt P₁, hP₁, Polynomial.coe_aeval_eq_eval, hPtj]
    exact hT (IsAlgebraic.restrictScalars (ZMod p) halgK₀)

  have hunit : IsUnit e := by
    by_contra hnu
    exact hπe ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have he0 : (e : FF) ≠ 0 := by
    intro h0; apply hπe
    have : e = 0 := Subtype.ext h0
    rw [this, map_zero]
  refine ⟨by rw [← hcoe]; exact e.2, ?_⟩
  rw [← hcoe]
  exact (isUnit_iff_inv_mem Vt e.2 he0).mp (by
    have : (⟨(e : FF), e.2⟩ : Vt) = e := Subtype.ext rfl
    rw [this]; exact hunit)

set_option maxHeartbeats 6400000 in

theorem complete (hpN : ¬ p ∣ N) (V : ValuationSubring FQ)
    (hpV : ((p : ℕ) : FQ) ∈ V.nonunits)
    (hjV : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
      P.eval₂ (algebraMap ℤ FQ) (jFQ N p) ∈ V ∧ (P.eval₂ (algebraMap ℤ FQ) (jFQ N p))⁻¹ ∈ V) :
    V = (W₀ : ValuationSubring FQ) ∨ V = W₁ := by
  obtain ⟨Vt, hVt⟩ := exists_valuationSubring_comap_eq (emb N p) V
  obtain ⟨hA'p, hG⟩ := liesOverPrime_and_isGaussOn_extension hpV hjV hVt
  obtain ⟨R, hmem, -, hR1, -, -, ⟨hj, hresj0, -, -, -, -⟩, hcomplete⟩ :=
    ModularCurve.exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd N p hpN
      (Vt.comap (algebraMap ℚ̄ FF)) hA'p
  have hG0 : IsGaussOn (Vt.comap (algebraMap ℚ̄ FF)) (R 0).integers (jFF N p) :=
    isGaussOn_regularProlongation (R 0) (hj 0) hresj0
  have hV' : ∀ e ∈ IntermediateField.adjoin ℚ̄ ({jFF N p} : Set FF), e ∈ Vt ↔ e ∈ (R 0).integers :=
    IsGaussOn.mem_iff_mem hG hG0
  have hgauss := fun f => emb_mem_gauss_iff (N := N) (p := p) hA'p (R 0).integers (R 0).algebraMap_mem_iff hmem f
  rcases hcomplete Vt hV' with h0 | h1
  · left; ext f
    rw [hVt, h0]; exact hgauss f
  · right; ext f
    rw [hVt, h1, mem_gaussZ'_iff]
    rw [hR1 (emb N p f), geomAut_emb]
    exact hgauss (w f)

variable (N p)

set_option maxHeartbeats 6400000 in
theorem main (hpN : ¬ p ∣ N) :
    ∃ W : Fin 2 → ValuationSubring FQ,
      (∀ f : FQ, f ∈ W 0 ↔ ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) ∧
      (∀ f : FQ, f ∈ W 1 ↔ atkinLehnerInvolutionFull N p f ∈ W 0) ∧
      W 0 ≠ W 1 ∧
      (∀ i, ((p : ℕ) : FQ) ∈ (W i).nonunits ∧
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          P.eval₂ (algebraMap ℤ FQ) (jFQ N p) ∈ W i ∧ (P.eval₂ (algebraMap ℤ FQ) (jFQ N p))⁻¹ ∈ W i) ∧
        (∀ f ∈ (W i).nonunits, f * ((p : ℕ) : FQ)⁻¹ ∈ W i)) ∧
      ∀ V : ValuationSubring FQ, ((p : ℕ) : FQ) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          P.eval₂ (algebraMap ℤ FQ) (jFQ N p) ∈ V ∧ (P.eval₂ (algebraMap ℤ FQ) (jFQ N p))⁻¹ ∈ V) →
        V = W 0 ∨ V = W 1 := by
  refine ⟨![gaussZ p (N * p), gaussZ' N p], fun f => Iff.rfl, fun f => Iff.rfl,
    gaussZ_ne_gaussZ' N p hpN, Fin.forall_fin_two.mpr ⟨props_gaussZ N p, props_gaussZ' N p hpN⟩,
    fun V hpV hjV => complete hpN V hpV hjV⟩

end Descent

end NeronLeg1TwoBranchesQ
p2m_reactivate "P2MW.S_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd.NeronLeg1TwoBranchesQ"

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    ∃ W : Fin 2 → ValuationSubring ↥(ModularCurve.modularFunctionFieldFull (N * p)),

      (∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W 0 ↔
        ∃ x y : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * ModularCurve.coeffMap (Int.castRingHom ℚ) y
            = ModularCurve.coeffMap (Int.castRingHom ℚ) x) ∧

      (∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W 1 ↔
        ModularCurve.atkinLehnerInvolutionFull N p f ∈ W 0) ∧

      W 0 ≠ W 1 ∧

      (∀ i, ((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ∈ (W i).nonunits ∧
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P ∈ W i ∧
            (Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P)⁻¹ ∈ W i) ∧
        (∀ f ∈ (W i).nonunits,
          f * ((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p)))⁻¹ ∈ W i)) ∧

      ∀ V : ValuationSubring ↥(ModularCurve.modularFunctionFieldFull (N * p)),
        ((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P ∈ V ∧
            (Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P)⁻¹ ∈ V) →
        V = W 0 ∨ V = W 1 :=
  NeronLeg1TwoBranchesQ.main N p hpN

end
p2m_reactivate "P2MW.S_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd.NeronLeg1TwoBranchesQ"

end S_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd (solution)
