-- Prove2me | solution 1 for ModularCurve.coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4e2c79a4-c9c3-5491-8865-778e6a4b33e4

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul_map
import Theorems.Thm_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D
import Theorems.Thm_AlgebraicCurve_isTraceDiff_traceDiff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd.ModularCurve AlgebraicCurve IntermediateField"

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof heckeAlphaC coe_heckeAlphaC heckeBetaC coe_heckeBetaC jqModC modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd dedekindPsi thetaL thetaL_apply qExpansionDiffAlong qExpandAlgHomC modularFunctionFieldFullC coeff_jqModC_neg_one qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qExpand theta_coeff charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul modularFunctionFieldC_eq_modularFunctionFieldFullC relfinrank_modularFunctionFieldFullC_mul_dedekindPsi dedekindPsi_pos isSeparable_jqNModC_of_natCast_ne_zero kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC isQExpansionDiffAlong_qExpansionDiffAlong qExpansionDiffAlong_smul_map qExpansionDiff_traceDiff_pullbackDiff_smul_D"
namespace CharQHeckeUDiff
p2m_open "ModularCurve"

section Laurent

variable {K : Type*} [Field K]

theorem thetaL_coeff (f : LaurentSeries K) (n : ℤ) :
    (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply, theta_coeff, zsmul_eq_mul]

theorem thetaL_qExpand (m : ℕ) [NeZero m] (x : LaurentSeries K) :
    thetaL K (qExpand K m x) = (m : K) • qExpand K m (thetaL K x) := by
  ext n
  rw [thetaL_coeff, HahnSeries.coeff_smul, smul_eq_mul]
  by_cases hn : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [qExpand_coeff_mul, qExpand_coeff_mul, thetaL_coeff]
    push_cast
    ring
  · rw [qExpand_coeff_of_not_dvd m _ hn, qExpand_coeff_of_not_dvd m _ hn, mul_zero, mul_zero]

theorem qTwist_qExpand_of_pow_eq_one (m : ℕ) [NeZero m] {u : Kˣ} (hu : u ^ m = 1)
    (x : LaurentSeries K) : qTwist u (qExpand K m x) = qExpand K m x := by
  rw [qTwist_qExpand, zpow_natCast, hu, qTwist_one_apply]

theorem sum_qTwist_coeff (ℓ : ℕ) [Fact ℓ.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (x : LaurentSeries K) (k : ℤ) :
    (∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) x).coeff k =
      if (ℓ : ℤ) ∣ k then (ℓ : K) * x.coeff k else 0 := by
  have hcoeff : (∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) x).coeff k =
      (∑ b ∈ Finset.range ℓ, (((ζ : Kˣ) ^ k : Kˣ) : K) ^ b) * x.coeff k := by
    rw [HahnSeries.coeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [qTwist_coeff]
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm]
  rw [hcoeff]
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp hζ
  by_cases hk : (ℓ : ℤ) ∣ k
  · rw [if_pos hk]
    obtain ⟨m, rfl⟩ := hk
    have h1 : ((ζ ^ ((ℓ : ℤ) * m) : Kˣ) : K) = 1 := by
      rw [zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow, Units.val_one]
    rw [h1]
    simp
  · rw [if_neg hk]
    have hne : ((ζ ^ k : Kˣ) : K) ≠ 1 := by
      intro h1
      apply hk
      have h2 : (ζ : Kˣ) ^ k = 1 := Units.val_eq_one.mp h1
      exact (hζu.zpow_eq_one_iff_dvd k).mp h2
    have hgeom : (∑ b ∈ Finset.range ℓ, (((ζ : Kˣ) ^ k : Kˣ) : K) ^ b) = 0 := by
      have hmul := geom_sum_mul (((ζ ^ k : Kˣ) : K)) ℓ
      have hpow : (((ζ ^ k : Kˣ) : K)) ^ ℓ = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
          zpow_natCast, hζu.pow_eq_one, one_zpow, Units.val_one]
      rw [hpow, sub_self] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hne)
    rw [hgeom, zero_mul]

theorem natCast_ne_zero_of_isPrimitiveRoot (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) : (ℓ : K) ≠ 0 := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact (hζ.neZero' (n := ℓ)).out

theorem zeta_pow_pow (ℓ : ℕ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) : (ζ ^ b) ^ ℓ = 1 := by
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp hζ
  rw [← pow_mul, mul_comm, pow_mul, hζu.pow_eq_one, one_pow]

end Laurent

section Psi

theorem dedekindPsi_mul_of_prime_dvd {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (hN : N ≠ 0) :
    dedekindPsi (N * ℓ) = ℓ * dedekindPsi N := by
  have hNℓ : N * ℓ ≠ 0 := mul_ne_zero hN hℓ.ne_zero
  have hset : (N * ℓ).divisors.filter Squarefree = N.divisors.filter Squarefree := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, hsq⟩
      refine ⟨⟨?_, hN⟩, hsq⟩
      by_cases hℓd : ℓ ∣ d
      · obtain ⟨e, rfl⟩ := hℓd
        obtain ⟨N', rfl⟩ := hℓN
        have hℓe : ¬ ℓ ∣ e := by
          rintro ⟨e', rfl⟩
          have hu : IsUnit ℓ := hsq ℓ ⟨e', by ring⟩
          exact hℓ.one_lt.ne' (Nat.isUnit_iff.mp hu)
        have hcop : Nat.Coprime e ℓ :=
          (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓe)
        have h1 : e ∣ N' * ℓ := by
          have h2 : ℓ * e ∣ ℓ * (N' * ℓ) := by
            have h3 : ℓ * (N' * ℓ) = ℓ * N' * ℓ := by ring
            rw [h3]; exact hd
          exact (Nat.mul_dvd_mul_iff_left hℓ.pos).mp h2
        exact mul_dvd_mul_left ℓ (hcop.dvd_of_dvd_mul_right h1)
      · have hcop : Nat.Coprime d ℓ :=
          (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓd)
        exact hcop.dvd_of_dvd_mul_right hd
    · rintro ⟨⟨hd, -⟩, hsq⟩
      exact ⟨⟨Dvd.dvd.mul_right hd ℓ, hNℓ⟩, hsq⟩
  rw [dedekindPsi, dedekindPsi, hset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨⟨c, hc⟩, -⟩, -⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hc; exact hN hc)
  rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0, mul_comm]

end Psi

section Degrees

variable (K : Type*) [Field K] (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

theorem not_ringChar_dvd (M : ℕ) (hM : (M : K) ≠ 0) : ¬ ringChar K ∣ M := fun h =>
  hM ((ringChar.spec K M).mpr h)

theorem modularFunctionFieldC_eq_fullC (hN : (N : K) ≠ 0) :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N :=
  haveI : CharP K (ringChar K) := ringChar.charP K
  modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) N (not_ringChar_dvd K N hN)

theorem roof_eq_fullC (hN : (N : K) ≠ 0) (hℓK : (ℓ : K) ≠ 0) :
    charLDegeneracyRoof K N ℓ = modularFunctionFieldFullC K (N * ℓ) := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  refine charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K (ringChar K) N ℓ ?_
  apply not_ringChar_dvd K (N * ℓ)
  push_cast
  exact mul_ne_zero hN hℓK

def betaField : IntermediateField K (LaurentSeries K) :=
  (modularFunctionFieldC K N).map (qExpandAlgHomC K ℓ)

theorem coe_heckeBetaC_mem (f : modularFunctionFieldC K N) :
    ((heckeBetaC K N ℓ f : charLDegeneracyRoof K N ℓ) : LaurentSeries K) ∈ betaField K N ℓ :=
  ⟨f, f.2, rfl⟩

theorem betaField_le_roof : betaField K N ℓ ≤ charLDegeneracyRoof K N ℓ := by
  rintro x ⟨y, hy, rfl⟩
  exact (heckeBetaC K N ℓ ⟨y, hy⟩).2

theorem relfinrank_betaField_roof (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    IntermediateField.relfinrank (betaField K N ℓ) (charLDegeneracyRoof K N ℓ) = ℓ := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩
  have hNℓK : ((N * ℓ : ℕ) : K) ≠ 0 := by push_cast; exact mul_ne_zero hN hℓK
  have h := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi K N ℓ hNℓK).2
  rw [← modularFunctionFieldC_eq_fullC K N hN, ← roof_eq_fullC K N ℓ hN hℓK,
    dedekindPsi_mul_of_prime_dvd hℓ.out hℓN (NeZero.ne N)] at h
  exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos N (NeZero.ne N)) h

theorem finrank_along_beta (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    letI := algebraAlong (heckeBetaC K N ℓ)
    Module.finrank (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) = ℓ := by
  letI := algebraAlong (heckeBetaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  refine Eq.trans ?_ (relfinrank_betaField_roof K N ℓ hN hℓN hℓK)
  rw [relfinrank_eq_finrank_of_le (betaField_le_roof K N ℓ)]
  let i : modularFunctionFieldC K N ≃+* betaField K N ℓ :=
    ((modularFunctionFieldC K N).equivMap (qExpandAlgHomC K ℓ)).toRingEquiv
  let jj : charLDegeneracyRoof K N ℓ ≃+* extendScalars (betaField_le_roof K N ℓ) :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  refine Algebra.finrank_eq_of_equiv_equiv (R₀ := modularFunctionFieldC K N)
    (S₀ := charLDegeneracyRoof K N ℓ) (R₁ := betaField K N ℓ)
    (S₁ := extendScalars (betaField_le_roof K N ℓ)) i jj ?_
  refine RingHom.ext fun a => Subtype.ext ?_
  rfl

end Degrees

section Trace

variable (K : Type*) [Field K] (N ℓ : ℕ)

def Lβ (_K : Type*) [Field _K] (_N _ℓ : ℕ) : Type _ := LaurentSeries _K

scoped instance instFieldLβ : Field (Lβ K N ℓ) := inferInstanceAs (Field (LaurentSeries K))

def toLβ : LaurentSeries K ≃+* Lβ K N ℓ := RingEquiv.refl _

variable [NeZero N] [hℓ : Fact ℓ.Prime]

scoped instance algFLβ : Algebra (modularFunctionFieldC K N) (Lβ K N ℓ) :=
  ((toLβ K N ℓ).toRingHom.comp ((qExpand K ℓ).comp
    (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)))).toAlgebra

theorem algebraMap_FLβ (f : modularFunctionFieldC K N) :
    algebraMap (modularFunctionFieldC K N) (Lβ K N ℓ) f = toLβ K N ℓ (qExpand K ℓ (f : LaurentSeries K)) :=
  rfl

abbrev Ebar : Type _ := AlgebraicClosure (Lβ K N ℓ)

abbrev ιE : LaurentSeries K →+* Ebar K N ℓ :=
  (algebraMap (Lβ K N ℓ) (Ebar K N ℓ)).comp (toLβ K N ℓ).toRingHom

omit [NeZero N] hℓ in
theorem ιE_injective : Function.Injective (ιE K N ℓ) :=
  (algebraMap (Lβ K N ℓ) (Ebar K N ℓ)).injective.comp (toLβ K N ℓ).injective

theorem algebraMap_FE (f : modularFunctionFieldC K N) :
    algebraMap (modularFunctionFieldC K N) (Ebar K N ℓ) f = ιE K N ℓ (qExpand K ℓ (f : LaurentSeries K)) := by
  rw [IsScalarTower.algebraMap_apply (modularFunctionFieldC K N) (Lβ K N ℓ) (Ebar K N ℓ), algebraMap_FLβ]
  rfl

def embTwist (u : Kˣ) (hu : u ^ ℓ = 1) :
    letI := algebraAlong (heckeBetaC K N ℓ)
    charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ :=
  letI := algebraAlong (heckeBetaC K N ℓ)
  { (ιE K N ℓ).comp ((qTwist u).comp (algebraMap (charLDegeneracyRoof K N ℓ) (LaurentSeries K))) with
    commutes' := fun f => by
      rw [algebraMap_FE]
      show ιE K N ℓ (qTwist u ((heckeBetaC K N ℓ f : charLDegeneracyRoof K N ℓ) : LaurentSeries K)) = _
      rw [coe_heckeBetaC, qTwist_qExpand_of_pow_eq_one ℓ hu] }

theorem embTwist_apply (u : Kˣ) (hu : u ^ ℓ = 1) (x : charLDegeneracyRoof K N ℓ) :
    embTwist K N ℓ u hu x = ιE K N ℓ (qTwist u (x : LaurentSeries K)) :=
  rfl

def emb (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : Fin ℓ) :
    letI := algebraAlong (heckeBetaC K N ℓ)
    charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ :=
  embTwist K N ℓ (ζ ^ (b : ℕ)) (zeta_pow_pow ℓ ζ hζ b)

theorem emb_apply (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : Fin ℓ) (x : charLDegeneracyRoof K N ℓ) :
    emb K N ℓ ζ hζ b x = ιE K N ℓ (qTwist (ζ ^ (b : ℕ)) (x : LaurentSeries K)) :=
  rfl

abbrev jF : modularFunctionFieldC K N := ⟨jqModC K, jqModC_mem K N⟩

theorem emb_injective (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    Function.Injective (emb K N ℓ ζ hζ) := by
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp hζ
  have hTw : ∀ b : ℕ, (qTwist (ζ ^ b) ((heckeAlphaC K N ℓ (jF K N) : charLDegeneracyRoof K N ℓ) :
      LaurentSeries K)).coeff (-1) = (((ζ ^ b) ^ (-1 : ℤ) : Kˣ) : K) := by
    intro b
    rw [coe_heckeAlphaC, qTwist_coeff, coeff_jqModC_neg_one, mul_one]
  intro b b' hbb'
  have hval := congrArg (fun s => s (heckeAlphaC K N ℓ (jF K N))) hbb'
  try simp only at hval
  rw [emb_apply, emb_apply] at hval
  have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) (ιE_injective K N ℓ hval)
  try simp only at h
  rw [hTw, hTw, Units.val_inj, zpow_neg, zpow_neg, inv_inj, zpow_one, zpow_one] at h
  exact Fin.ext (hζu.pow_inj b.2 b'.2 h)

theorem isSeparable_and_bijective (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    letI := algebraAlong (heckeBetaC K N ℓ)
    Algebra.IsSeparable (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) ∧
      Function.Bijective (emb K N ℓ ζ hζ) := by
  letI := algebraAlong (heckeBetaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  have hfr := finrank_along_beta K N ℓ hN hℓN hℓK
  haveI : FiniteDimensional (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hℓ.out.pos)
  haveI : Algebra.IsAlgebraic (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hinj := emb_injective K N ℓ ζ hζ
  have hle : Nat.card (charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ) ≤ ℓ := by
    have h := Field.finSepDegree_le_finrank (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
    rw [hfr, Field.finSepDegree_eq_of_isAlgClosed (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
      (Ebar K N ℓ)] at h
    exact h
  have hge : ℓ ≤ Nat.card (charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hcard : Nat.card (charLDegeneracyRoof K N ℓ →ₐ[modularFunctionFieldC K N] Ebar K N ℓ) = ℓ :=
    le_antisymm hle hge
  refine ⟨?_, ?_⟩
  · rw [← Field.finSepDegree_eq_finrank_iff, hfr,
      Field.finSepDegree_eq_of_isAlgClosed (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) (Ebar K N ℓ)]
    exact hcard
  · rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, hcard]

theorem qExpand_trace (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (y : charLDegeneracyRoof K N ℓ) :
    letI := algebraAlong (heckeBetaC K N ℓ)
    qExpand K ℓ ((Algebra.trace (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) y :
        modularFunctionFieldC K N) : LaurentSeries K) =
      ∑ b : Fin ℓ, qTwist (ζ ^ (b : ℕ)) (y : LaurentSeries K) := by
  letI := algebraAlong (heckeBetaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  have hfr := finrank_along_beta K N ℓ hN hℓN hℓK
  haveI : FiniteDimensional (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hℓ.out.pos)
  obtain ⟨hsep, hbij⟩ := isSeparable_and_bijective K N ℓ hN hℓN ζ hζ
  haveI := hsep
  apply ιE_injective K N ℓ
  have htr := trace_eq_sum_embeddings (Ebar K N ℓ) (K := modularFunctionFieldC K N)
    (L := charLDegeneracyRoof K N ℓ) (x := y)
  rw [algebraMap_FE] at htr
  rw [htr, ← Fintype.sum_bijective _ hbij (fun b => emb K N ℓ ζ hζ b y) (fun σ => σ y)
    (fun _ => rfl), map_sum]
  rfl

end Trace

section KaehlerGeneric

variable {K F R L : Type*} [Field K] [Field F] [Field R] [Algebra K F] [Algebra K R]
  [Field L] [Algebra K L]

theorem D_ne_zero_of_thetaL_ne_zero (σ : F →ₐ[K] LaurentSeries L) (x : F)
    (hx : thetaL L (σ x) ≠ 0) : KaehlerDifferential.D K F x ≠ 0 := by
  intro h0
  have h1 := (isQExpansionDiffAlong_qExpansionDiffAlong σ).1 x
  rw [h0, map_zero] at h1
  exact hx h1.symm

variable [Algebra F R] [IsScalarTower K F R]

theorem exists_D_eq_smul_map [Algebra.IsSeparable F R] (x : F)
    (hspan : ∀ ω : Ω[F⁄K], ∃ c : F, c • KaehlerDifferential.D K F x = ω) (b : R) :
    ∃ h : R, KaehlerDifferential.D K R b =
      h • KaehlerDifferential.map K K F R (KaehlerDifferential.D K F x) := by
  haveI : Algebra.FormallyEtale F R := Algebra.FormallyEtale.of_isSeparable F R
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange K F R) := fun z => by
    obtain ⟨t, ht⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F R).surjective z
    exact ⟨t, by rw [← ht, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]⟩
  have hall : ∀ t : TensorProduct F R (Ω[F⁄K]), ∃ h : R,
      KaehlerDifferential.mapBaseChange K F R t =
        h • KaehlerDifferential.map K K F R (KaehlerDifferential.D K F x) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
    | tmul r ω =>
      obtain ⟨c, rfl⟩ := hspan ω
      refine ⟨r * algebraMap F R c, ?_⟩
      rw [KaehlerDifferential.mapBaseChange_tmul, map_smul, ← IsScalarTower.algebraMap_smul R c,
        smul_smul]
    | add x y hx hy =>
      obtain ⟨h₁, h₁e⟩ := hx
      obtain ⟨h₂, h₂e⟩ := hy
      exact ⟨h₁ + h₂, by rw [map_add, h₁e, h₂e, add_smul]⟩
  obtain ⟨t, ht⟩ := hsurj (KaehlerDifferential.D K R b)
  obtain ⟨h, hh⟩ := hall t
  exact ⟨h, by rw [← ht, hh]⟩

theorem thetaL_eq_of_D_eq_smul_map (σ : R →ₐ[K] LaurentSeries L) {x : F} {b h : R}
    (hD : KaehlerDifferential.D K R b =
      h • KaehlerDifferential.map K K F R (KaehlerDifferential.D K F x)) :
    thetaL L (σ b) = σ h * thetaL L (σ (algebraMap F R x)) := by
  have h1 := (isQExpansionDiffAlong_qExpansionDiffAlong σ).1 b
  rw [hD, qExpansionDiffAlong_smul_map, (isQExpansionDiffAlong_qExpansionDiffAlong _).1 x] at h1
  exact h1.symm

theorem qExpansionDiffAlong_smul_D (σ : F →ₐ[K] LaurentSeries L) (f x : F) :
    qExpansionDiffAlong σ (f • KaehlerDifferential.D K F x) = σ f * thetaL L (σ x) := by
  rw [(isQExpansionDiffAlong_qExpansionDiffAlong σ).2, (isQExpansionDiffAlong_qExpansionDiffAlong σ).1]

end KaehlerGeneric

section Main

variable {K : Type*} [Field K]

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  try simp only at h1
  rw [thetaL_coeff, coeff_jqModC_neg_one, HahnSeries.coeff_zero, mul_one] at h1
  norm_num at h1

variable (K) (N ℓ : ℕ) [NeZero N] [hℓ : Fact ℓ.Prime]

omit hℓ in

theorem exists_eq_smul_D_jF (hN : (N : K) ≠ 0) (ω : Ω[modularFunctionFieldC K N⁄K]) :
    ∃ f : modularFunctionFieldC K N,
      f • KaehlerDifferential.D K (modularFunctionFieldC K N) (jF K N) = ω := by
  have hsep := isSeparable_jqNModC_of_natCast_ne_zero K N hN
  obtain ⟨_, hfin⟩ := kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC K N hsep
  have hDne := D_ne_zero_of_thetaL_ne_zero (modularFunctionFieldC K N).val (jF K N)
    (thetaL_jqModC_ne_zero K)
  exact (finrank_eq_one_iff_of_nonzero' _ hDne).mp hfin ω

theorem smul_qExpand_qExpansion_heckeU (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (ω : Ω[modularFunctionFieldC K N⁄K]) :
    letI := algebraAlong (heckeBetaC K N ℓ)
    haveI := isScalarTower_along (heckeBetaC K N ℓ)
    (ℓ : K) • qExpand K ℓ (qExpansionDiffAlong (modularFunctionFieldC K N).val
      (traceDiff K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (pullbackDiff (heckeAlphaC K N ℓ) ω))) =
      ∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) := by
  letI := algebraAlong (heckeBetaC K N ℓ)
  letI : Module (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) := Algebra.toModule
  haveI := isScalarTower_along (heckeBetaC K N ℓ)
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  obtain ⟨hsep, _⟩ := isSeparable_and_bijective K N ℓ hN hℓN ζ hζ
  haveI := hsep
  obtain ⟨f, rfl⟩ := exists_eq_smul_D_jF K N hN ω
  obtain ⟨h, hD⟩ := exists_D_eq_smul_map (K := K) (F := modularFunctionFieldC K N)
    (R := charLDegeneracyRoof K N ℓ) (jF K N) (exists_eq_smul_D_jF K N hN) (heckeAlphaC K N ℓ (jF K N))

  have hE1 : thetaL K (jqModC K) = (h : LaurentSeries K) * ((ℓ : K) • qExpand K ℓ (thetaL K (jqModC K))) := by
    have h1 := thetaL_eq_of_D_eq_smul_map (charLDegeneracyRoof K N ℓ).val hD
    have e1 : (charLDegeneracyRoof K N ℓ).val (heckeAlphaC K N ℓ (jF K N)) = jqModC K :=
      coe_heckeAlphaC K N ℓ (jF K N)
    have e2 : (charLDegeneracyRoof K N ℓ).val
        (algebraMap (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ) (jF K N)) =
          qExpand K ℓ (jqModC K) := rfl
    rw [e1, e2, thetaL_qExpand] at h1
    exact h1
  have key := qExpansionDiff_traceDiff_pullbackDiff_smul_D
    (isQExpansionDiffAlong_qExpansionDiffAlong (modularFunctionFieldC K N).val)
    (isTraceDiff_traceDiff K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)) (heckeAlphaC K N ℓ) hD f

  have hH := qExpansionDiffAlong_smul_D (modularFunctionFieldC K N).val f (jF K N)
  have hT1 := qExpand_trace K N ℓ hN hℓN ζ hζ (heckeAlphaC K N ℓ f * h)
  have hyval : ((heckeAlphaC K N ℓ f * h : charLDegeneracyRoof K N ℓ) : LaurentSeries K) =
      (f : LaurentSeries K) * (h : LaurentSeries K) := by
    rw [IntermediateField.coe_mul, coe_heckeAlphaC]
  rw [← HahnSeries.C_mul_eq_smul] at hE1
  have hTC : ∀ (u : Kˣ) (c : K), qTwist u (HahnSeries.C c) = HahnSeries.C c := by
    intro u c
    rw [HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]
  have hTV : ∀ b : ℕ, qTwist (ζ ^ b) (qExpand K ℓ (thetaL K (jqModC K))) = qExpand K ℓ (thetaL K (jqModC K)) :=
    fun b => qTwist_qExpand_of_pow_eq_one ℓ (zeta_pow_pow ℓ ζ hζ b) _

  have key' : qExpansionDiffAlong (modularFunctionFieldC K N).val
      (traceDiff K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (pullbackDiff (heckeAlphaC K N ℓ) (f • KaehlerDifferential.D K (modularFunctionFieldC K N) (jF K N)))) =
      ((Algebra.trace (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (heckeAlphaC K N ℓ f * h) : modularFunctionFieldC K N) : LaurentSeries K) * thetaL K (jqModC K) := key
  have hH' : qExpansionDiffAlong (modularFunctionFieldC K N).val
      (f • KaehlerDifferential.D K (modularFunctionFieldC K N) (jF K N)) =
      (f : LaurentSeries K) * thetaL K (jqModC K) := hH
  rw [key', hH', ← HahnSeries.C_mul_eq_smul, map_mul, hT1, hyval,
    Fin.sum_univ_eq_sum_range (fun b => qTwist (ζ ^ b) ((f : LaurentSeries K) * (h : LaurentSeries K))) ℓ,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  calc HahnSeries.C (ℓ : K) * (qTwist (ζ ^ b) ((f : LaurentSeries K) * (h : LaurentSeries K)) *
        qExpand K ℓ (thetaL K (jqModC K)))
      = qTwist (ζ ^ b) ((f : LaurentSeries K) *
          ((h : LaurentSeries K) * (HahnSeries.C (ℓ : K) * qExpand K ℓ (thetaL K (jqModC K))))) := by
        simp only [map_mul, hTC, hTV]
        ring
    _ = qTwist (ζ ^ b) ((f : LaurentSeries K) * thetaL K (jqModC K)) := by rw [← hE1]

theorem coeff_qExpansion_heckeU (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (ω : Ω[modularFunctionFieldC K N⁄K]) (n : ℤ) :
    (letI := AlgebraicCurve.algebraAlong (heckeBetaC K N ℓ)
     haveI := AlgebraicCurve.isScalarTower_along (heckeBetaC K N ℓ)
     qExpansionDiffAlong (modularFunctionFieldC K N).val
      (traceDiff K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (pullbackDiff (heckeAlphaC K N ℓ) ω))).coeff n
    = (qExpansionDiffAlong (modularFunctionFieldC K N).val ω).coeff ((ℓ : ℤ) * n) := by
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot ℓ ζ hζ
  have hV := smul_qExpand_qExpansion_heckeU K N ℓ hN hℓN ζ hζ ω
  have hc := congrArg (fun s : LaurentSeries K => s.coeff ((ℓ : ℤ) * n)) hV
  try simp only at hc
  rw [HahnSeries.coeff_smul, qExpand_coeff_mul, sum_qTwist_coeff ℓ ζ hζ, if_pos (Dvd.intro n rfl),
    smul_eq_mul] at hc
  exact mul_left_cancel₀ hℓK hc

end Main

end ModularCurve.CharQHeckeUDiff
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd.ModularCurve P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd.ModularCurve.CharQHeckeUDiff"
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd.ModularCurve AlgebraicCurve in
theorem solution
    (K : Type*) [Field K] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hN : (N : K) ≠ 0) (hℓN : ℓ ∣ N) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (ω : Ω[modularFunctionFieldC K N⁄K]) (n : ℤ) :
    (letI := AlgebraicCurve.algebraAlong (heckeBetaC K N ℓ)
     haveI := AlgebraicCurve.isScalarTower_along (heckeBetaC K N ℓ)
     qExpansionDiffAlong (modularFunctionFieldC K N).val
      (traceDiff K (modularFunctionFieldC K N) (charLDegeneracyRoof K N ℓ)
        (pullbackDiff (heckeAlphaC K N ℓ) ω))).coeff n
    = (qExpansionDiffAlong (modularFunctionFieldC K N).val ω).coeff ((ℓ : ℤ) * n) :=
  ModularCurve.CharQHeckeUDiff.coeff_qExpansion_heckeU K N ℓ hN hℓN ζ hζ ω n

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd.ModularCurve P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd.ModularCurve.CharQHeckeUDiff"

end S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd
end P2MW
export P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd (solution)
