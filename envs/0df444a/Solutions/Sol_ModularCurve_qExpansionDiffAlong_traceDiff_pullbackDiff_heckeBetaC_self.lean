-- Prove2me | solution 1 for ModularCurve.qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/678149f7-df2a-5fda-84e6-eb0359d3d3a6

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
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots
import Theorems.Thm_ModularCurve_modularFunctionFieldC_algHom_ext
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isQExpansionDiffAlong_qExpansionDiffAlong
import Theorems.Thm_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D
import Theorems.Thm_AlgebraicCurve_isTraceDiff_traceDiff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve AlgebraicCurve IntermediateField Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "charLDegeneracyRoof modularFunctionFieldC_le_charLDegeneracyRoof heckeAlphaC coe_heckeAlphaC heckeBetaC coe_heckeBetaC jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi thetaL thetaL_apply qExpansionDiffAlong qExpandAlgHomC modularFunctionFieldFullC jqModC_mem_full algebraMap_laurentSeries_eq_single coeff_jqModC_neg_one qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qExpand theta_coeff charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul modularFunctionFieldC_eq_modularFunctionFieldFullC finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi dedekindPsi_pos minpoly_jqNModC_map_eq_prod_slots modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_natCast_ne_zero kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC isQExpansionDiffAlong_qExpansionDiffAlong qExpansionDiff_traceDiff_pullbackDiff_smul_D"
namespace LevelHeckeDiff
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

theorem thetaL_qTwist (u : Kˣ) (x : LaurentSeries K) : thetaL K (qTwist u x) = qTwist u (thetaL K x) := by
  ext n
  rw [thetaL_coeff, qTwist_coeff, qTwist_coeff, thetaL_coeff]
  ring

theorem qTwist_qExpand_of_pow_eq_one (m : ℕ) [NeZero m] {u : Kˣ} (hu : u ^ m = 1)
    (x : LaurentSeries K) : qTwist u (qExpand K m x) = qExpand K m x := by
  rw [qTwist_qExpand, zpow_natCast, hu, qTwist_one_apply]

theorem natCast_ne_zero_of_isPrimitiveRoot (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) : (ℓ : K) ≠ 0 := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact (hζ.neZero' (n := ℓ)).out

theorem zeta_pow_pow (ℓ : ℕ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) : (ζ ^ b) ^ ℓ = 1 := by
  have hζu : IsPrimitiveRoot ζ ℓ := (IsPrimitiveRoot.coe_units_iff).mp hζ
  rw [← pow_mul, mul_comm, pow_mul, hζu.pow_eq_one, one_pow]

variable (K) in

def qTwistAlgHomC (u : Kˣ) : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qTwist u
  commutes' c := by
    show qTwist u (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
    rw [algebraMap_laurentSeries_eq_single, qTwist_single, zpow_zero, Units.val_one, one_mul]

@[scoped simp] theorem qTwistAlgHomC_apply (u : Kˣ) (x : LaurentSeries K) : qTwistAlgHomC K u x = qTwist u x := rfl

end Laurent

section Degrees

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

variable (K : Type*) [Field K]

abbrev A0 : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))

theorem finrank_adjoin_mk_eq_relfinrank (X : IntermediateField K (LaurentSeries K))
    (x : LaurentSeries K) (hx : x ∈ X) :
    Module.finrank (IntermediateField.adjoin K ({(⟨x, hx⟩ : ↥X)} : Set ↥X)) X =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({x} : Set (LaurentSeries K))) X := by
  have hle : IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) ≤ X :=
    adjoin_simple_le_iff.mpr hx
  rw [relfinrank_eq_finrank_of_le hle]
  set A' : IntermediateField K ↥X := IntermediateField.adjoin K ({(⟨x, hx⟩ : ↥X)} : Set ↥X)
  have hlift : lift A' = IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) :=
    IntermediateField.lift_adjoin_simple K X ⟨x, hx⟩
  let i : A' ≃+* IntermediateField.adjoin K ({x} : Set (LaurentSeries K)) :=
    ((liftAlgEquiv A').trans (equivOfEq hlift)).toRingEquiv
  let jj : X ≃+* extendScalars hle :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  refine Algebra.finrank_eq_of_equiv_equiv i jj ?_
  refine RingHom.ext fun a => Subtype.ext ?_
  rfl

theorem relfinrank_A0_fullC (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    IntermediateField.relfinrank (A0 K) (modularFunctionFieldFullC K M) = dedekindPsi M := by
  rw [← finrank_adjoin_mk_eq_relfinrank K (modularFunctionFieldFullC K M) (jqModC K)
    (jqModC_mem_full K M)]
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K M hM

theorem not_ringChar_dvd (M : ℕ) (hM : (M : K) ≠ 0) : ¬ ringChar K ∣ M := fun h =>
  hM ((ringChar.spec K M).mpr h)

theorem modularFunctionFieldC_eq_fullC (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    modularFunctionFieldC K M = modularFunctionFieldFullC K M :=
  haveI : CharP K (ringChar K) := ringChar.charP K
  modularFunctionFieldC_eq_modularFunctionFieldFullC K (ringChar K) M (not_ringChar_dvd K M hM)

theorem A0_le (M : ℕ) [NeZero M] : A0 K ≤ modularFunctionFieldC K M :=
  adjoin_simple_le_iff.mpr (jqModC_mem K M)

theorem adjoin_A0_eq_extendScalars (M : ℕ) [NeZero M] :
    IntermediateField.adjoin (A0 K) ({jqNModC K M} : Set (LaurentSeries K)) =
      extendScalars (A0_le K M) := by
  apply IntermediateField.restrictScalars_injective K
  erw [adjoin_adjoin_left]
  rw [Set.singleton_union]
  rfl

theorem finrank_A0_adjoin (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    Module.finrank (A0 K) (IntermediateField.adjoin (A0 K) ({jqNModC K M} : Set (LaurentSeries K))) =
      dedekindPsi M := by
  rw [adjoin_A0_eq_extendScalars, ← relfinrank_eq_finrank_of_le (A0_le K M),
    modularFunctionFieldC_eq_fullC K M hM]
  exact relfinrank_A0_fullC K M hM

variable (p : ℕ) [hpp : Fact p.Prime]

theorem roof_eq_fullC (hp : (p : K) ≠ 0) :
    charLDegeneracyRoof K p p = modularFunctionFieldFullC K (p * p) := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  refine charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K (ringChar K) p p ?_
  apply not_ringChar_dvd K (p * p)
  push_cast
  exact mul_ne_zero hp hp

theorem relfinrank_roof (hp : (p : K) ≠ 0) :
    IntermediateField.relfinrank (modularFunctionFieldC K p) (charLDegeneracyRoof K p p) = p := by
  have h1 : IntermediateField.relfinrank (A0 K) (modularFunctionFieldC K p) = dedekindPsi p := by
    rw [modularFunctionFieldC_eq_fullC K p hp]; exact relfinrank_A0_fullC K p hp
  have h2 : IntermediateField.relfinrank (A0 K) (charLDegeneracyRoof K p p) = dedekindPsi (p * p) := by
    rw [roof_eq_fullC K p hp]
    refine relfinrank_A0_fullC K (p * p) ?_
    push_cast; exact mul_ne_zero hp hp
  have hmul := relfinrank_mul_relfinrank (A0_le K p) (modularFunctionFieldC_le_charLDegeneracyRoof K p p)
  rw [h1, h2, dedekindPsi_mul_of_prime_dvd hpp.out dvd_rfl hpp.out.ne_zero, mul_comm p] at hmul
  exact Nat.eq_of_mul_eq_mul_left (dedekindPsi_pos p hpp.out.ne_zero) hmul

theorem finrank_along_alpha (hp : (p : K) ≠ 0) :
    letI := algebraAlong (heckeAlphaC K p p)
    Module.finrank (modularFunctionFieldC K p) (charLDegeneracyRoof K p p) = p := by
  letI := algebraAlong (heckeAlphaC K p p)
  letI : Module (modularFunctionFieldC K p) (charLDegeneracyRoof K p p) := Algebra.toModule
  refine Eq.trans ?_ (relfinrank_roof K p hp)
  rw [relfinrank_eq_finrank_of_le (modularFunctionFieldC_le_charLDegeneracyRoof K p p)]
  let jj : charLDegeneracyRoof K p p ≃+*
      extendScalars (modularFunctionFieldC_le_charLDegeneracyRoof K p p) :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  refine Algebra.finrank_eq_of_equiv_equiv (R₀ := modularFunctionFieldC K p)
    (S₀ := charLDegeneracyRoof K p p) (R₁ := modularFunctionFieldC K p)
    (S₁ := extendScalars (modularFunctionFieldC_le_charLDegeneracyRoof K p p)) (RingEquiv.refl _) jj ?_
  refine RingHom.ext fun a => Subtype.ext ?_
  show ((heckeAlphaC K p p a : charLDegeneracyRoof K p p) : LaurentSeries K) = a
  exact coe_heckeAlphaC K p p a

end Degrees

section MinPoly

variable (K : Type*) [Field K] (p : ℕ) [hpp : Fact p.Prime]

abbrev FF : Type _ := ↥(modularFunctionFieldC K p)
abbrev RR : Type _ := ↥(charLDegeneracyRoof K p p)

abbrev jF : FF K p := ⟨jqModC K, jqModC_mem K p⟩
abbrev jpF : FF K p := ⟨jqNModC K p, jqNModC_mem K p⟩

abbrev jP2 : LaurentSeries K := qExpand K (p * p) (jqModC K)

theorem jP2_mem : jP2 K p ∈ charLDegeneracyRoof K p p := by
  refine subset_adjoin K _ ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact Or.inr (Or.inr (Or.inr rfl))

abbrev yR : RR K p := ⟨jP2 K p, jP2_mem K p⟩

theorem hall (hp : (p : K) ≠ 0) : ∀ d : ℕ, d ∣ p → ∀ [NeZero d],
    Module.finrank (A0 K) (IntermediateField.adjoin (A0 K) ({jqNModC K d} : Set (LaurentSeries K))) =
        dedekindPsi d ∧
      modularFunctionFieldC K d = IntermediateField.adjoin K
        {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'} := by
  intro d hd _
  have hdK : (d : K) ≠ 0 := by
    intro h
    apply hp
    obtain ⟨c, rfl⟩ := hd
    push_cast
    rw [h, zero_mul]
  refine ⟨finrank_A0_adjoin K d hdK, ?_⟩
  rw [modularFunctionFieldC_eq_fullC K d hdK]
  rfl

theorem prod_slots_eq (ζ : Kˣ) :
    (∏ a ∈ p.divisors, ∏ b ∈ (Finset.range (p / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (p / a) = 1),
        (X - C (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩
          qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K))))) =
      (∏ b ∈ Finset.range p, (X - C (qTwist (ζ ^ b) (jqModC K)))) * (X - C (jP2 K p)) := by
  rw [Nat.Prime.divisors hpp.out, Finset.prod_pair hpp.out.one_lt.ne]
  congr 1
  · rw [Nat.div_one, Finset.filter_true_of_mem (fun b _ => by simp)]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [dif_neg one_ne_zero, qExpand_congr (mul_one 1), qExpand_one_apply, mul_one]
  · rw [Nat.div_self hpp.out.pos, Finset.range_one,
      Finset.filter_true_of_mem (fun b hb => by
        rw [Finset.mem_singleton] at hb; subst hb; simp),
      Finset.prod_singleton, dif_neg hpp.out.ne_zero, zero_mul, pow_zero, qTwist_one_apply]

theorem A0_map_le : (A0 K).map (qExpandAlgHomC K p) ≤ modularFunctionFieldC K p := by
  rw [adjoin_map, Set.image_singleton, adjoin_simple_le_iff]
  exact jqNModC_mem K p

theorem qExpand_mem_of_mem_A0 {x : LaurentSeries K} (hx : x ∈ A0 K) :
    qExpand K p x ∈ modularFunctionFieldC K p :=
  A0_map_le K p ((IntermediateField.map_mem_map (A0 K) (qExpandAlgHomC K p)).mpr hx)

def phi0 : A0 K →+* FF K p where
  toFun x := ⟨qExpand K p (x : LaurentSeries K), qExpand_mem_of_mem_A0 K p x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem algebraMap_comp_phi0 :
    (algebraMap (FF K p) (LaurentSeries K)).comp (phi0 K p) =
      (qExpand K p).comp (algebraMap (A0 K) (LaurentSeries K)) :=
  RingHom.ext fun _ => rfl

def PF : (FF K p)[X] := (minpoly (A0 K) (jqNModC K p)).map (phi0 K p)

variable (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
include hζ

theorem PF_map :
    (PF K p).map (algebraMap (FF K p) (LaurentSeries K)) =
      (∏ b ∈ Finset.range p, (X - C (qTwist (ζ ^ b) (jqModC K)))) * (X - C (jP2 K p)) := by
  have hp := natCast_ne_zero_of_isPrimitiveRoot p ζ hζ
  rw [PF, Polynomial.map_map, algebraMap_comp_phi0, ← prod_slots_eq K p ζ]
  exact minpoly_jqNModC_map_eq_prod_slots p ζ hζ (hall K p hp)

theorem PF_isRoot_jF : (PF K p).IsRoot (jF K p) := by
  have hinj := (algebraMap (FF K p) (LaurentSeries K)).injective
  rw [IsRoot.def]
  apply hinj
  rw [map_zero, ← eval₂_at_apply, ← eval_map, PF_map K p ζ hζ, eval_mul]
  apply mul_eq_zero_of_left
  rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hpp.out.pos)
  rw [pow_zero, qTwist_one_apply, eval_sub, eval_X, eval_C]
  exact sub_self _

omit hζ in

def QF : (FF K p)[X] := PF K p /ₘ (X - C (jF K p))

def Qexp : (LaurentSeries K)[X] :=
  (∏ b ∈ (Finset.range p).erase 0, (X - C (qTwist (ζ ^ b) (jqModC K)))) * (X - C (jP2 K p))

omit hζ in
theorem monic_Qexp : (Qexp K p ζ).Monic :=
  (monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).mul (monic_X_sub_C _)

omit hζ in
theorem natDegree_Qexp : (Qexp K p ζ).natDegree = p := by
  rw [Qexp, (monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).natDegree_mul (monic_X_sub_C _),
    natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _), natDegree_X_sub_C]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hpp.out.pos), Finset.card_range]
  have := hpp.out.one_lt
  omega

theorem QF_map : (QF K p).map (algebraMap (FF K p) (LaurentSeries K)) = Qexp K p ζ := by
  have hfac : (X - C (jF K p)) * QF K p = PF K p := mul_divByMonic_eq_iff_isRoot.mpr (PF_isRoot_jF K p ζ hζ)
  have h1 : (X - C (jqModC K)) * (QF K p).map (algebraMap (FF K p) (LaurentSeries K)) =
      (X - C (jqModC K)) * Qexp K p ζ := by
    have h2 := congrArg (Polynomial.map (algebraMap (FF K p) (LaurentSeries K))) hfac
    rw [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, PF_map K p ζ hζ] at h2
    have h3 : algebraMap (FF K p) (LaurentSeries K) (jF K p) = jqModC K := rfl
    rw [h3] at h2
    rw [h2, Qexp, ← mul_assoc, ← Finset.mul_prod_erase (Finset.range p)
      (fun b => X - C (qTwist (ζ ^ b) (jqModC K))) (Finset.mem_range.mpr hpp.out.pos), pow_zero,
      qTwist_one_apply]
  exact mul_left_cancel₀ (X_sub_C_ne_zero _) h1

omit hζ in
theorem monic_QF_of (h : (QF K p).map (algebraMap (FF K p) (LaurentSeries K)) = Qexp K p ζ) :
    (QF K p).Monic :=
  monic_of_injective (algebraMap (FF K p) (LaurentSeries K)).injective (by rw [h]; exact monic_Qexp K p ζ)

omit hζ in

theorem eval_Qexp_jP2 : (Qexp K p ζ).eval (jP2 K p) = 0 := by
  rw [Qexp, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero]

omit hζ in
theorem eval_Qexp_qTwist {b : ℕ} (hb : b ∈ (Finset.range p).erase 0) :
    (Qexp K p ζ).eval (qTwist (ζ ^ b) (jqModC K)) = 0 := by
  rw [Qexp, eval_mul]
  apply mul_eq_zero_of_left
  rw [eval_prod]
  apply Finset.prod_eq_zero hb
  rw [eval_sub, eval_X, eval_C, sub_self]

omit hζ in
theorem isScalarTower_FRL :
    letI := algebraAlong (heckeAlphaC K p p)
    IsScalarTower (FF K p) (RR K p) (LaurentSeries K) := by
  letI := algebraAlong (heckeAlphaC K p p)
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  show (x : LaurentSeries K) = ((heckeAlphaC K p p x : RR K p) : LaurentSeries K)
  exact (coe_heckeAlphaC K p p x).symm

omit hζ in
theorem coe_algebraMap_FR (x : FF K p) :
    letI := algebraAlong (heckeAlphaC K p p)
    ((algebraMap (FF K p) (RR K p) x : RR K p) : LaurentSeries K) = x := by
  show ((heckeAlphaC K p p x : RR K p) : LaurentSeries K) = x
  exact coe_heckeAlphaC K p p x

omit hζ in
theorem finite_FR (hp : (p : K) ≠ 0) :
    letI := algebraAlong (heckeAlphaC K p p)
    Module.Finite (FF K p) (RR K p) := by
  letI := algebraAlong (heckeAlphaC K p p)
  letI : Module (FF K p) (RR K p) := Algebra.toModule
  exact Module.finite_of_finrank_pos (by rw [finrank_along_alpha K p hp]; exact hpp.out.pos)

omit hζ in
theorem isIntegral_yR (hp : (p : K) ≠ 0) :
    letI := algebraAlong (heckeAlphaC K p p)
    IsIntegral (FF K p) (yR K p) := by
  letI := algebraAlong (heckeAlphaC K p p)
  haveI := finite_FR K p hp
  exact IsIntegral.of_finite (FF K p) (yR K p)

theorem aeval_yR_QF :
    letI := algebraAlong (heckeAlphaC K p p)
    aeval (yR K p) (QF K p) = 0 := by
  letI := algebraAlong (heckeAlphaC K p p)
  haveI := isScalarTower_FRL K p
  let ψ : RR K p →ₐ[FF K p] LaurentSeries K := IsScalarTower.toAlgHom (FF K p) (RR K p) (LaurentSeries K)
  have hinj : Function.Injective ψ := (ψ : RR K p →+* LaurentSeries K).injective
  apply hinj
  rw [map_zero, ← aeval_algHom_apply, aeval_def, ← eval_map, QF_map K p ζ hζ]
  exact eval_Qexp_jP2 K p ζ

omit hζ in

theorem adjoin_yR_eq_top :
    letI := algebraAlong (heckeAlphaC K p p)
    IntermediateField.adjoin (FF K p) ({yR K p} : Set (RR K p)) = ⊤ := by
  letI := algebraAlong (heckeAlphaC K p p)
  haveI : IsScalarTower K (FF K p) (RR K p) := isScalarTower_along (heckeAlphaC K p p)
  set T : IntermediateField (FF K p) (RR K p) := IntermediateField.adjoin (FF K p) ({yR K p} : Set (RR K p))
  have hle : charLDegeneracyRoof K p p ≤ IntermediateField.lift (T.restrictScalars K) := by
    unfold charLDegeneracyRoof
    rw [adjoin_le_iff]
    have hgen : ∀ (x : FF K p), ((x : LaurentSeries K)) ∈ IntermediateField.lift (T.restrictScalars K) := by
      intro x
      have hx : (⟨(x : LaurentSeries K), modularFunctionFieldC_le_charLDegeneracyRoof K p p x.2⟩ : RR K p) =
          algebraMap (FF K p) (RR K p) x := by
        refine Subtype.ext ?_
        rw [coe_algebraMap_FR]
      have h := (IntermediateField.mem_lift (E := T.restrictScalars K)
        (⟨(x : LaurentSeries K), modularFunctionFieldC_le_charLDegeneracyRoof K p p x.2⟩ : RR K p)).mpr
        (by
          change (⟨(x : LaurentSeries K), modularFunctionFieldC_le_charLDegeneracyRoof K p p x.2⟩ : RR K p) ∈ T
          rw [hx]; exact IntermediateField.algebraMap_mem T x)
      exact h
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hgen (jF K p)
    · exact hgen (jpF K p)
    · exact hgen (jpF K p)
    · exact (IntermediateField.mem_lift (E := T.restrictScalars K) (yR K p)).mpr
        (by change yR K p ∈ T; exact mem_adjoin_simple_self _ _)
  have heq : IntermediateField.lift (T.restrictScalars K) = charLDegeneracyRoof K p p :=
    le_antisymm (lift_le _) hle
  have htop : T.restrictScalars K = ⊤ := by
    apply IntermediateField.lift_injective
    rw [heq]
    exact (IntermediateField.lift_top K (charLDegeneracyRoof K p p)).symm
  apply IntermediateField.restrictScalars_injective K
  rw [htop, restrictScalars_top]

theorem minpoly_yR :
    letI := algebraAlong (heckeAlphaC K p p)
    minpoly (FF K p) (yR K p) = QF K p := by
  letI := algebraAlong (heckeAlphaC K p p)
  letI : Module (FF K p) (RR K p) := Algebra.toModule
  have hp := natCast_ne_zero_of_isPrimitiveRoot p ζ hζ
  have hy := isIntegral_yR K p hp
  have hdeg : (minpoly (FF K p) (yR K p)).natDegree = p := by
    rw [← adjoin.finrank hy, adjoin_yR_eq_top K p, finrank_top', finrank_along_alpha K p hp]
  have hdegQ : (QF K p).natDegree = p := by
    rw [← natDegree_map_eq_of_injective (algebraMap (FF K p) (LaurentSeries K)).injective, QF_map K p ζ hζ,
      natDegree_Qexp]
  symm
  exact eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hy) (monic_QF_of K p ζ (QF_map K p ζ hζ))
    (minpoly.dvd _ _ (aeval_yR_QF K p ζ hζ)) (by rw [hdeg, hdegQ])

def root (i : Fin p) : LaurentSeries K :=
  if (i : ℕ) = 0 then jP2 K p else qTwist (ζ ^ (i : ℕ)) (jqModC K)

omit hζ in
theorem root_zero_val (i : Fin p) (hi : (i : ℕ) = 0) : root K p ζ i = jP2 K p := if_pos hi

omit hζ in
theorem root_ne_val (i : Fin p) (hi : (i : ℕ) ≠ 0) : root K p ζ i = qTwist (ζ ^ (i : ℕ)) (jqModC K) := if_neg hi

theorem root_mem_aroots (i : Fin p) :
    letI := algebraAlong (heckeAlphaC K p p)
    root K p ζ i ∈ (minpoly (FF K p) (yR K p)).aroots (LaurentSeries K) := by
  letI := algebraAlong (heckeAlphaC K p p)
  have hp := natCast_ne_zero_of_isPrimitiveRoot p ζ hζ
  rw [mem_aroots, minpoly_yR K p ζ hζ]
  refine ⟨(monic_QF_of K p ζ (QF_map K p ζ hζ)).ne_zero, ?_⟩
  rw [aeval_def, ← eval_map, QF_map K p ζ hζ]
  by_cases hi : (i : ℕ) = 0
  · rw [root_zero_val K p ζ i hi]; exact eval_Qexp_jP2 K p ζ
  · rw [root_ne_val K p ζ i hi]
    exact eval_Qexp_qTwist K p ζ (Finset.mem_erase.mpr ⟨hi, Finset.mem_range.mpr i.2⟩)

theorem root_injective : Function.Injective (root K p ζ) := by
  have hζu : IsPrimitiveRoot ζ p := (IsPrimitiveRoot.coe_units_iff).mp hζ
  have hnot : ¬ ((p * p : ℕ) : ℤ) ∣ -1 := by
    intro h
    have h1 : ((p * p : ℕ) : ℤ) ∣ 1 := (dvd_neg).mp h
    have h2 : p * p ∣ 1 := by exact_mod_cast h1
    have := Nat.dvd_one.mp h2
    exact hpp.out.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right this)
  have h0 : (jP2 K p).coeff (-1) = 0 := qExpand_coeff_of_not_dvd (p * p) _ hnot
  have hb : ∀ b : ℕ, (qTwist (ζ ^ b) (jqModC K)).coeff (-1) = (((ζ ^ b) ^ (-1 : ℤ) : Kˣ) : K) := by
    intro b
    rw [qTwist_coeff, coeff_jqModC_neg_one, mul_one]
  intro i i' hii'
  by_cases hi : (i : ℕ) = 0
  · by_cases hi' : (i' : ℕ) = 0
    · exact Fin.ext (hi.trans hi'.symm)
    · exfalso
      rw [root_zero_val K p ζ i hi, root_ne_val K p ζ i' hi'] at hii'
      have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) hii'
      rw [h0, hb] at h
      exact (Units.ne_zero _) h.symm
  · by_cases hi' : (i' : ℕ) = 0
    · exfalso
      rw [root_ne_val K p ζ i hi, root_zero_val K p ζ i' hi'] at hii'
      have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) hii'
      rw [h0, hb] at h
      exact (Units.ne_zero _) h
    · rw [root_ne_val K p ζ i hi, root_ne_val K p ζ i' hi'] at hii'
      have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) hii'
      rw [hb, hb, Units.val_inj, zpow_neg, zpow_neg, inv_inj, zpow_one, zpow_one] at h
      exact Fin.ext (hζu.pow_inj i.2 i'.2 h)

end MinPoly

section Embeddings

variable (K : Type*) [Field K] (p : ℕ) [hpp : Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)

def toAdjoin :
    letI := algebraAlong (heckeAlphaC K p p)
    RR K p ≃ₐ[FF K p] IntermediateField.adjoin (FF K p) ({yR K p} : Set (RR K p)) :=
  letI := algebraAlong (heckeAlphaC K p p)
  ((equivOfEq (adjoin_yR_eq_top K p)).trans topEquiv).symm

theorem toAdjoin_yR :
    letI := algebraAlong (heckeAlphaC K p p)
    toAdjoin K p (yR K p) = AdjoinSimple.gen (FF K p) (yR K p) := by
  exact Subtype.ext rfl

def emb (i : Fin p) :
    letI := algebraAlong (heckeAlphaC K p p)
    RR K p →ₐ[FF K p] LaurentSeries K :=
  letI := algebraAlong (heckeAlphaC K p p)
  ((algHomAdjoinIntegralEquiv (FF K p) (isIntegral_yR K p (natCast_ne_zero_of_isPrimitiveRoot p ζ hζ))).symm
      ⟨root K p ζ i, root_mem_aroots K p ζ hζ i⟩).comp
    (toAdjoin K p : RR K p →ₐ[FF K p] IntermediateField.adjoin (FF K p) ({yR K p} : Set (RR K p)))

theorem emb_yR (i : Fin p) : emb K p ζ hζ i (yR K p) = root K p ζ i := by
  letI := algebraAlong (heckeAlphaC K p p)
  unfold emb
  rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, toAdjoin_yR, algHomAdjoinIntegralEquiv_symm_apply_gen]

theorem emb_algebraMap (i : Fin p) (x : FF K p) :
    letI := algebraAlong (heckeAlphaC K p p)
    emb K p ζ hζ i (algebraMap (FF K p) (RR K p) x) = x := by
  letI := algebraAlong (heckeAlphaC K p p)
  exact (emb K p ζ hζ i).commutes x

abbrev Ebar : Type _ := AlgebraicClosure (LaurentSeries K)

def embE (i : Fin p) :
    letI := algebraAlong (heckeAlphaC K p p)
    RR K p →ₐ[FF K p] Ebar K :=
  letI := algebraAlong (heckeAlphaC K p p)
  (IsScalarTower.toAlgHom (FF K p) (LaurentSeries K) (Ebar K)).comp (emb K p ζ hζ i)

theorem embE_apply (i : Fin p) (z : RR K p) :
    embE K p ζ hζ i z = algebraMap (LaurentSeries K) (Ebar K) (emb K p ζ hζ i z) := rfl

theorem embE_injective : Function.Injective (embE K p ζ hζ) := by
  intro i i' hii'
  apply root_injective K p ζ hζ
  have h := congrArg (fun s => s (yR K p)) hii'
  simp only [embE_apply, emb_yR] at h
  exact (algebraMap (LaurentSeries K) (Ebar K)).injective h

theorem isSeparable_and_bijective :
    letI := algebraAlong (heckeAlphaC K p p)
    Algebra.IsSeparable (FF K p) (RR K p) ∧ Function.Bijective (embE K p ζ hζ) := by
  letI := algebraAlong (heckeAlphaC K p p)
  letI : Module (FF K p) (RR K p) := Algebra.toModule
  have hp : (p : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot p ζ hζ
  have hfr := finrank_along_alpha K p hp
  haveI : FiniteDimensional (FF K p) (RR K p) := finite_FR K p hp
  haveI : Algebra.IsAlgebraic (FF K p) (RR K p) := Algebra.IsAlgebraic.of_finite _ _
  have hinj := embE_injective K p ζ hζ
  have hle : Nat.card (RR K p →ₐ[FF K p] Ebar K) ≤ p := by
    have h1 := Field.finSepDegree_le_finrank (FF K p) (RR K p)
    rw [hfr] at h1
    rw [← Field.finSepDegree_eq_of_isAlgClosed (FF K p) (RR K p) (Ebar K)]
    exact h1
  have hge : p ≤ Nat.card (RR K p →ₐ[FF K p] Ebar K) := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hcard : Nat.card (RR K p →ₐ[FF K p] Ebar K) = p := le_antisymm hle hge
  refine ⟨?_, ?_⟩
  · rw [← Field.finSepDegree_eq_finrank_iff, hfr,
      Field.finSepDegree_eq_of_isAlgClosed (FF K p) (RR K p) (Ebar K)]
    exact hcard
  · rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, hcard]

theorem coe_trace (z : RR K p) :
    letI := algebraAlong (heckeAlphaC K p p)
    ((Algebra.trace (FF K p) (RR K p) z : FF K p) : LaurentSeries K) = ∑ i : Fin p, emb K p ζ hζ i z := by
  letI := algebraAlong (heckeAlphaC K p p)
  letI : Module (FF K p) (RR K p) := Algebra.toModule
  have hp : (p : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot p ζ hζ
  haveI : FiniteDimensional (FF K p) (RR K p) := finite_FR K p hp
  obtain ⟨hsep, hbij⟩ := isSeparable_and_bijective K p ζ hζ
  haveI := hsep
  apply (algebraMap (LaurentSeries K) (Ebar K)).injective
  have htr := trace_eq_sum_embeddings (Ebar K) (K := FF K p) (L := RR K p) (x := z)
  rw [IsScalarTower.algebraMap_apply (FF K p) (LaurentSeries K) (Ebar K)] at htr
  change algebraMap (LaurentSeries K) (Ebar K) ((Algebra.trace (FF K p) (RR K p) z : FF K p) : LaurentSeries K)
    = _ at htr
  rw [htr, ← Fintype.sum_bijective _ hbij (fun i => embE K p ζ hζ i z) (fun σ => σ z) (fun _ => rfl), map_sum]
  rfl

end Embeddings

section Beta

variable (K : Type*) [Field K] (p : ℕ) [hpp : Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
variable (τ : modularFunctionFieldC K p ≃ₐ[K] modularFunctionFieldC K p)
  (hτ₁ : τ ⟨jqModC K, jqModC_mem K p⟩ = ⟨jqNModC K p, jqNModC_mem K p⟩)
  (hτ₂ : τ ⟨jqNModC K p, jqNModC_mem K p⟩ = ⟨jqModC K, jqModC_mem K p⟩)

include hζ hτ₁ hτ₂

omit hζ hτ₁ hτ₂ in
theorem heckeBetaC_jF :
    letI := algebraAlong (heckeAlphaC K p p)
    heckeBetaC K p p (jF K p) = algebraMap (FF K p) (RR K p) (jpF K p) := by
  refine Subtype.ext ?_
  rw [coe_heckeBetaC, coe_algebraMap_FR]
  rfl

omit hζ hτ₁ hτ₂ in
theorem heckeBetaC_jpF : heckeBetaC K p p (jpF K p) = yR K p := by
  refine Subtype.ext ?_
  rw [coe_heckeBetaC]
  exact qExpand_qExpand p p (jqModC K)

theorem emb_heckeBetaC (i : Fin p) (u : FF K p) :
    emb K p ζ hζ i (heckeBetaC K p p u) =
      if (i : ℕ) = 0 then qExpand K p (u : LaurentSeries K)
      else qTwist (ζ ^ (i : ℕ)) ((τ u : FF K p) : LaurentSeries K) := by
  letI := algebraAlong (heckeAlphaC K p p)
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi]
    have key : ((emb K p ζ hζ i).restrictScalars K).comp (heckeBetaC K p p) =
        (qExpandAlgHomC K p).comp (modularFunctionFieldC K p).val := by
      refine modularFunctionFieldC_algHom_ext K p ?_ ?_
      · show emb K p ζ hζ i (heckeBetaC K p p (jF K p)) = qExpand K p (jqModC K)
        rw [heckeBetaC_jF, emb_algebraMap]
        rfl
      · show emb K p ζ hζ i (heckeBetaC K p p (jpF K p)) = qExpand K p (jqNModC K p)
        rw [heckeBetaC_jpF, emb_yR, root_zero_val K p ζ i hi]
        exact (qExpand_qExpand p p (jqModC K)).symm
    exact congrArg (fun g : modularFunctionFieldC K p →ₐ[K] LaurentSeries K => g u) key
  · rw [if_neg hi]
    have key : ((emb K p ζ hζ i).restrictScalars K).comp (heckeBetaC K p p) =
        (qTwistAlgHomC K (ζ ^ (i : ℕ))).comp
          ((modularFunctionFieldC K p).val.comp (τ : FF K p →ₐ[K] FF K p)) := by
      refine modularFunctionFieldC_algHom_ext K p ?_ ?_
      · show emb K p ζ hζ i (heckeBetaC K p p (jF K p)) =
          qTwist (ζ ^ (i : ℕ)) ((τ (jF K p) : FF K p) : LaurentSeries K)
        rw [heckeBetaC_jF, emb_algebraMap]
        change jqNModC K p = _
        rw [show ((τ (jF K p) : FF K p) : LaurentSeries K) = jqNModC K p from congrArg Subtype.val hτ₁]
        exact (qTwist_qExpand_of_pow_eq_one p (zeta_pow_pow p ζ hζ i) (jqModC K)).symm
      · show emb K p ζ hζ i (heckeBetaC K p p (jpF K p)) =
          qTwist (ζ ^ (i : ℕ)) ((τ (jpF K p) : FF K p) : LaurentSeries K)
        rw [heckeBetaC_jpF, emb_yR, root_ne_val K p ζ i hi,
          show ((τ (jpF K p) : FF K p) : LaurentSeries K) = jqModC K from congrArg Subtype.val hτ₂]
    exact congrArg (fun g : modularFunctionFieldC K p →ₐ[K] LaurentSeries K => g u) key

theorem coe_trace_heckeBetaC (u : FF K p) :
    letI := algebraAlong (heckeAlphaC K p p)
    ((Algebra.trace (FF K p) (RR K p) (heckeBetaC K p p u) : FF K p) : LaurentSeries K) =
      qExpand K p (u : LaurentSeries K) +
        ∑ b ∈ Finset.Ico 1 p, qTwist (ζ ^ b) ((τ u : FF K p) : LaurentSeries K) := by
  rw [coe_trace K p ζ hζ]
  have h1 : (∑ i : Fin p, emb K p ζ hζ i (heckeBetaC K p p u)) =
      ∑ b ∈ Finset.range p, (if b = 0 then qExpand K p (u : LaurentSeries K)
        else qTwist (ζ ^ b) ((τ u : FF K p) : LaurentSeries K)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => emb_heckeBetaC K p ζ hζ τ hτ₁ hτ₂ i u
  have hIco : Finset.Ico 1 p = (Finset.range p).erase 0 := by
    ext b; simp only [Finset.mem_Ico, Finset.mem_erase, Finset.mem_range]; omega
  rw [h1, ← Finset.add_sum_erase (Finset.range p) _ (Finset.mem_range.mpr hpp.out.pos), if_pos rfl, hIco]
  congr 1
  exact Finset.sum_congr rfl fun b hb => if_neg (Finset.mem_erase.mp hb).1

end Beta

section Main

variable {K : Type*} [Field K]

theorem qTwist_smul (u : Kˣ) (c : K) (x : LaurentSeries K) : qTwist u (c • x) = c • qTwist u x := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, map_mul, HahnSeries.C_apply, qTwist_single,
    zpow_zero, Units.val_one, one_mul]

theorem qExpand_smul (m : ℕ) [NeZero m] (c : K) (x : LaurentSeries K) :
    qExpand K m (c • x) = c • qExpand K m x := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, map_mul, qExpand_C]

theorem thetaL_jqModC_ne_zero (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  rw [thetaL_coeff, coeff_jqModC_neg_one, HahnSeries.coeff_zero, mul_one] at h1
  norm_num at h1

theorem D_ne_zero_of_thetaL_ne_zero {F L : Type*} [Field F] [Algebra K F] [Field L] [Algebra K L]
    (σ : F →ₐ[K] LaurentSeries L) (x : F)
    (hx : thetaL L (σ x) ≠ 0) : KaehlerDifferential.D K F x ≠ 0 := by
  intro h0
  have h1 := (isQExpansionDiffAlong_qExpansionDiffAlong σ).1 x
  rw [h0, map_zero] at h1
  exact hx h1.symm

theorem qExpansionDiffAlong_smul_D {F L : Type*} [Field F] [Algebra K F] [Field L] [Algebra K L]
    (σ : F →ₐ[K] LaurentSeries L) (f x : F) :
    qExpansionDiffAlong σ (f • KaehlerDifferential.D K F x) = σ f * thetaL L (σ x) := by
  rw [(isQExpansionDiffAlong_qExpansionDiffAlong σ).2, (isQExpansionDiffAlong_qExpansionDiffAlong σ).1]

variable (K) (p : ℕ) [hpp : Fact p.Prime]

theorem exists_eq_smul_D_jF (hp : (p : K) ≠ 0) (ω : Ω[modularFunctionFieldC K p⁄K]) :
    ∃ f : modularFunctionFieldC K p,
      f • KaehlerDifferential.D K (modularFunctionFieldC K p) (jF K p) = ω := by
  have hsep := isSeparable_jqNModC_of_natCast_ne_zero K p hp
  obtain ⟨_, hfin⟩ := kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC K p hsep
  have hDne := D_ne_zero_of_thetaL_ne_zero (modularFunctionFieldC K p).val (jF K p)
    (thetaL_jqModC_ne_zero K)
  exact (finrank_eq_one_iff_of_nonzero' _ hDne).mp hfin ω

variable (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
variable (τ : modularFunctionFieldC K p ≃ₐ[K] modularFunctionFieldC K p)
  (hτ₁ : τ ⟨jqModC K, jqModC_mem K p⟩ = ⟨jqNModC K p, jqNModC_mem K p⟩)
  (hτ₂ : τ ⟨jqNModC K p, jqNModC_mem K p⟩ = ⟨jqModC K, jqModC_mem K p⟩)

include hζ hτ₁ hτ₂

theorem main (ω : Ω[modularFunctionFieldC K p⁄K]) :
    (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K p p)
     haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K p p)
     qExpansionDiffAlong (modularFunctionFieldC K p).val
      (traceDiff K (modularFunctionFieldC K p) (charLDegeneracyRoof K p p)
        (pullbackDiff (heckeBetaC K p p) ω)))
    = (p : K) • qExpand K p (qExpansionDiffAlong (modularFunctionFieldC K p).val ω)
      + ∑ b ∈ Finset.Ico 1 p, qTwist (ζ ^ b)
          (qExpansionDiffAlong ((modularFunctionFieldC K p).val.comp (τ : FF K p →ₐ[K] FF K p)) ω) := by
  letI := algebraAlong (heckeAlphaC K p p)
  letI : Module (FF K p) (RR K p) := Algebra.toModule
  haveI := isScalarTower_along (heckeAlphaC K p p)
  have hp : (p : K) ≠ 0 := natCast_ne_zero_of_isPrimitiveRoot p ζ hζ
  obtain ⟨hsep, _⟩ := isSeparable_and_bijective K p ζ hζ
  haveI := hsep
  obtain ⟨u, rfl⟩ := exists_eq_smul_D_jF K p hp ω
  obtain ⟨h, hh⟩ := exists_eq_smul_D_jF K p hp (KaehlerDifferential.D K (FF K p) (jpF K p))

  have hD : KaehlerDifferential.D K (RR K p) (heckeBetaC K p p (jF K p)) =
      algebraMap (FF K p) (RR K p) h •
        KaehlerDifferential.map K K (FF K p) (RR K p) (KaehlerDifferential.D K (FF K p) (jF K p)) := by
    rw [heckeBetaC_jF, ← KaehlerDifferential.map_D K K (FF K p) (RR K p) (jpF K p), ← hh, LinearMap.map_smul,
      algebraMap_smul (RR K p)]
  have key := qExpansionDiff_traceDiff_pullbackDiff_smul_D
    (isQExpansionDiffAlong_qExpansionDiffAlong (modularFunctionFieldC K p).val)
    (isTraceDiff_traceDiff K (FF K p) (RR K p)) (heckeBetaC K p p) hD u

  have htr : Algebra.trace (FF K p) (RR K p) (heckeBetaC K p p u * algebraMap (FF K p) (RR K p) h) =
      h * Algebra.trace (FF K p) (RR K p) (heckeBetaC K p p u) := by
    rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

  have hθp : ((h : FF K p) : LaurentSeries K) * thetaL K (jqModC K) =
      (p : K) • qExpand K p (thetaL K (jqModC K)) := by
    have h1 := congrArg (qExpansionDiffAlong (modularFunctionFieldC K p).val) hh
    have h2 : qExpansionDiffAlong (modularFunctionFieldC K p).val
        (h • KaehlerDifferential.D K (modularFunctionFieldC K p) (jF K p)) =
        ((h : FF K p) : LaurentSeries K) * thetaL K (jqModC K) :=
      qExpansionDiffAlong_smul_D (modularFunctionFieldC K p).val h (jF K p)
    have h3 : qExpansionDiffAlong (modularFunctionFieldC K p).val
        (KaehlerDifferential.D K (modularFunctionFieldC K p) (jpF K p)) = thetaL K (jqNModC K p) :=
      (isQExpansionDiffAlong_qExpansionDiffAlong (modularFunctionFieldC K p).val).1 (jpF K p)
    rw [h2, h3] at h1
    rw [h1]
    exact thetaL_qExpand p (jqModC K)
  have hτj : ((τ (jF K p) : FF K p) : LaurentSeries K) = jqNModC K p := congrArg Subtype.val hτ₁

  have key2 : qExpansionDiffAlong (modularFunctionFieldC K p).val
      (traceDiff K (FF K p) (RR K p)
        (pullbackDiff (heckeBetaC K p p) (u • KaehlerDifferential.D K (FF K p) (jF K p)))) =
      ((h * Algebra.trace (FF K p) (RR K p) (heckeBetaC K p p u) : FF K p) : LaurentSeries K) *
        thetaL K (jqModC K) :=
    key.trans (congrArg (fun t : FF K p => (t : LaurentSeries K) * thetaL K (jqModC K)) htr)
  have hL : qExpansionDiffAlong (modularFunctionFieldC K p).val
      (traceDiff K (FF K p) (RR K p)
        (pullbackDiff (heckeBetaC K p p) (u • KaehlerDifferential.D K (FF K p) (jF K p)))) =
      (qExpand K p (u : LaurentSeries K) +
        ∑ b ∈ Finset.Ico 1 p, qTwist (ζ ^ b) ((τ u : FF K p) : LaurentSeries K)) *
        ((p : K) • qExpand K p (thetaL K (jqModC K))) := by
    rw [key2, IntermediateField.coe_mul, coe_trace_heckeBetaC K p ζ hζ τ hτ₁ hτ₂ u, mul_right_comm, hθp,
      mul_comm]
  have hR1 : qExpansionDiffAlong (modularFunctionFieldC K p).val (u • KaehlerDifferential.D K (FF K p) (jF K p)) =
      (u : LaurentSeries K) * thetaL K (jqModC K) :=
    qExpansionDiffAlong_smul_D (modularFunctionFieldC K p).val u (jF K p)
  have hR2 : qExpansionDiffAlong ((modularFunctionFieldC K p).val.comp (τ : FF K p →ₐ[K] FF K p))
      (u • KaehlerDifferential.D K (FF K p) (jF K p)) =
      ((τ u : FF K p) : LaurentSeries K) * ((p : K) • qExpand K p (thetaL K (jqModC K))) := by
    refine (qExpansionDiffAlong_smul_D ((modularFunctionFieldC K p).val.comp (τ : FF K p →ₐ[K] FF K p))
      u (jF K p)).trans ?_
    change ((τ u : FF K p) : LaurentSeries K) * thetaL K ((τ (jF K p) : FF K p) : LaurentSeries K) = _
    rw [hτj]
    exact congrArg _ (thetaL_qExpand p (jqModC K))
  change qExpansionDiffAlong (modularFunctionFieldC K p).val
      (traceDiff K (FF K p) (RR K p)
        (pullbackDiff (heckeBetaC K p p) (u • KaehlerDifferential.D K (FF K p) (jF K p)))) =
    (p : K) • qExpand K p (qExpansionDiffAlong (modularFunctionFieldC K p).val
        (u • KaehlerDifferential.D K (FF K p) (jF K p)))
      + ∑ b ∈ Finset.Ico 1 p, qTwist (ζ ^ b)
          (qExpansionDiffAlong ((modularFunctionFieldC K p).val.comp (τ : FF K p →ₐ[K] FF K p))
            (u • KaehlerDifferential.D K (FF K p) (jF K p)))
  rw [hL, hR1, hR2, add_mul, Finset.sum_mul]
  simp only [← HahnSeries.C_mul_eq_smul]
  have hTC : ∀ (v : Kˣ) (c : K), qTwist v (HahnSeries.C c) = HahnSeries.C c := by
    intro v c
    rw [HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]
  congr 1
  · rw [map_mul]; ring
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, hTC, qTwist_qExpand_of_pow_eq_one p (zeta_pow_pow p ζ hζ b)]

end Main

end ModularCurve.LevelHeckeDiff
p2m_reactivate "P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve.LevelHeckeDiff"
p2m_reactivate "P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve.LevelHeckeDiff"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve AlgebraicCurve in
theorem solution
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (τ : modularFunctionFieldC K p ≃ₐ[K] modularFunctionFieldC K p)
    (hτ₁ : τ ⟨jqModC K, jqModC_mem K p⟩ = ⟨jqNModC K p, jqNModC_mem K p⟩)
    (hτ₂ : τ ⟨jqNModC K p, jqNModC_mem K p⟩ = ⟨jqModC K, jqModC_mem K p⟩)
    (ω : Ω[modularFunctionFieldC K p⁄K]) :
    (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K p p)
     haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K p p)
     qExpansionDiffAlong (modularFunctionFieldC K p).val
      (traceDiff K (modularFunctionFieldC K p) (charLDegeneracyRoof K p p)
        (pullbackDiff (heckeBetaC K p p) ω)))
    = (p : K) • qExpand K p (qExpansionDiffAlong (modularFunctionFieldC K p).val ω)
      + ∑ b ∈ Finset.Ico 1 p, qTwist (ζ ^ b)
          (qExpansionDiffAlong ((modularFunctionFieldC K p).val.comp
            (τ : modularFunctionFieldC K p →ₐ[K] modularFunctionFieldC K p)) ω) :=
  ModularCurve.LevelHeckeDiff.main K p ζ hζ τ hτ₁ hτ₂ ω

end S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self
end P2MW
export P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self (solution)
