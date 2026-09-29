-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f291cbc5-e1dd-5a0d-9953-627ca1d4122a

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jq coeffMap coeffMap_coeff coeffMap_single coeffEmb coeffEmb_coeff laurentBaseChange coeffMap_ofPowerSeries jqModC instAlgebraIntermediateFieldLaurent exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC laurentBaseChange_qExpFunctionFieldC_eq"
namespace GaussExistsAlpha
p2m_open "ModularCurve"

scoped instance (p : ℕ) [hp : Fact p.Prime] : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out

theorem maximalIdeal_eq (p : ℕ) [hp : Fact p.Prime] :
    IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) = Ideal.span {(p : ↥(GaloisRep.ratLocalizedAt p))} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p hp.out

theorem ratLocalizedAtResidue_eq_zero_iff (p : ℕ) [hp : Fact p.Prime] (r : ↥(GaloisRep.ratLocalizedAt p)) :
    GaloisRep.ratLocalizedAtResidue p r = 0 ↔ r ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) := by
  constructor
  · intro hr
    by_contra h
    have hu : IsUnit r := by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
    exact (hu.map (GaloisRep.ratLocalizedAtResidue p)).ne_zero hr
  · intro hr
    rw [maximalIdeal_eq, Ideal.mem_span_singleton] at hr
    obtain ⟨s, rfl⟩ := hr
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem residue_eq_zero_iff' (p : ℕ) [hp : Fact p.Prime] (r : ↥(GaloisRep.ratLocalizedAt p)) :
    IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p) r = 0 ↔ GaloisRep.ratLocalizedAtResidue p r = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, ratLocalizedAtResidue_eq_zero_iff]

theorem map_residue_eq_zero_iff (p : ℕ) [hp : Fact p.Prime] (y : PowerSeries ↥(GaloisRep.ratLocalizedAt p)) :
    y.map (IsLocalRing.residue ↥(GaloisRep.ratLocalizedAt p)) = 0 ↔ y.map (GaloisRep.ratLocalizedAtResidue p) = 0 := by
  constructor <;> intro h <;> ext n <;> have hn := congrArg (PowerSeries.coeff n) h <;>
    simp only [PowerSeries.coeff_map, map_zero] at hn ⊢
  · exact (residue_eq_zero_iff' p _).mp hn
  · exact (residue_eq_zero_iff' p _).mpr hn

theorem coeffEmb_rat (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  ext k
  rw [coeffEmb_coeff]
  rfl

theorem ofPowerSeries_coeff_of_neg' {R : Type*} [Semiring R] (f : PowerSeries R) {k : ℤ}
    (hk : k < 0) : (HahnSeries.ofPowerSeries ℤ R f).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact absurd hk (not_lt.mpr (Int.natCast_nonneg m))

theorem coeffMap_ofPowerSeries {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (Y : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A Y) = HahnSeries.ofPowerSeries ℤ B (Y.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ofPowerSeries_coeff_of_neg' Y hk, ofPowerSeries_coeff_of_neg' (Y.map f) hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem exists_powerSeries_of_forall_coeff_neg_eq_zero {A : Type*} [CommRing A] (y : LaurentSeries A)
    (hy : ∀ n : ℤ, n < 0 → y.coeff n = 0) :
    ∃ Y : PowerSeries A, HahnSeries.ofPowerSeries ℤ A Y = y := by
  refine ⟨PowerSeries.mk fun n => y.coeff n, HahnSeries.ext (funext fun k => ?_)⟩
  rcases lt_or_ge k 0 with hk | hk
  · rw [hy k hk]
    exact ofPowerSeries_coeff_of_neg' (PowerSeries.mk fun n => y.coeff n) hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem exists_single_mul_coeff_neg_eq_zero {A : Type*} [CommRing A] (y : LaurentSeries A) :
    ∃ N : ℕ, ∀ n : ℤ, n < 0 → (HahnSeries.single (N : ℤ) (1 : A) * y).coeff n = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, fun n _ => by rw [mul_zero, HahnSeries.coeff_zero]⟩
  refine ⟨(-y.order).toNat, fun n hn => ?_⟩
  rw [HahnSeries.coeff_single_mul, one_mul]
  apply HahnSeries.coeff_eq_zero_of_lt_order
  omega

theorem exists_single_mul_coeff_neg_eq_zero₂ {A : Type*} [CommRing A] (a b : LaurentSeries A) :
    ∃ N : ℕ, (∀ n : ℤ, n < 0 → (HahnSeries.single (N : ℤ) (1 : A) * a).coeff n = 0) ∧
      (∀ n : ℤ, n < 0 → (HahnSeries.single (N : ℤ) (1 : A) * b).coeff n = 0) := by
  obtain ⟨Na, ha⟩ := exists_single_mul_coeff_neg_eq_zero a
  obtain ⟨Nb, hb⟩ := exists_single_mul_coeff_neg_eq_zero b
  refine ⟨Na + Nb, fun n hn => ?_, fun n hn => ?_⟩
  · rw [show ((Na + Nb : ℕ) : ℤ) = (Nb : ℤ) + (Na : ℤ) from by push_cast; ring,
      ← show HahnSeries.single (Nb : ℤ) (1 : A) * HahnSeries.single (Na : ℤ) 1 = HahnSeries.single ((Nb : ℤ) + Na) 1 from by
        rw [HahnSeries.single_mul_single, mul_one], mul_assoc, HahnSeries.coeff_single_mul, one_mul]
    exact ha _ (by omega)
  · rw [show ((Na + Nb : ℕ) : ℤ) = (Na : ℤ) + (Nb : ℤ) from by push_cast; ring,
      ← show HahnSeries.single (Na : ℤ) (1 : A) * HahnSeries.single (Nb : ℤ) 1 = HahnSeries.single ((Na : ℤ) + Nb) 1 from by
        rw [HahnSeries.single_mul_single, mul_one], mul_assoc, HahnSeries.coeff_single_mul, one_mul]
    exact hb _ (by omega)

section Main

variable (p : ℕ) [hp : Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem laurent_of_powerSeries (x : LaurentSeries ℚ) (a a' : PowerSeries (↥(GaloisRep.ratLocalizedAt p)))
    (ha' : a'.map (IsLocalRing.residue (↥(GaloisRep.ratLocalizedAt p))) ≠ 0)
    (h : x * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ)) = HahnSeries.ofPowerSeries ℤ ℚ (a.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ))) :
    ∃ c b : LaurentSeries (↥(GaloisRep.ratLocalizedAt p)), coeffMap (GaloisRep.ratLocalizedAtResidue p) b ≠ 0 ∧
      x * coeffMap (GaloisRep.ratLocalizedAt p).subtype b = coeffMap (GaloisRep.ratLocalizedAt p).subtype c := by
  refine ⟨HahnSeries.ofPowerSeries ℤ (↥(GaloisRep.ratLocalizedAt p)) a, HahnSeries.ofPowerSeries ℤ (↥(GaloisRep.ratLocalizedAt p)) a', ?_, ?_⟩
  · rw [coeffMap_ofPowerSeries]
    intro h0
    apply ha'
    rw [map_residue_eq_zero_iff]
    exact HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
  · rw [coeffMap_ofPowerSeries, coeffMap_ofPowerSeries]
    exact h

theorem powerSeries_of_laurent (x : LaurentSeries ℚ) (c b : LaurentSeries (↥(GaloisRep.ratLocalizedAt p)))
    (hb : coeffMap (GaloisRep.ratLocalizedAtResidue p) b ≠ 0)
    (h : x * coeffMap (GaloisRep.ratLocalizedAt p).subtype b = coeffMap (GaloisRep.ratLocalizedAt p).subtype c) :
    ∃ a a' : PowerSeries (↥(GaloisRep.ratLocalizedAt p)), a'.map (IsLocalRing.residue (↥(GaloisRep.ratLocalizedAt p))) ≠ 0 ∧
      x * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ)) = HahnSeries.ofPowerSeries ℤ ℚ (a.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ)) := by
  obtain ⟨N, hc, hb'⟩ := exists_single_mul_coeff_neg_eq_zero₂ c b
  obtain ⟨a, ha⟩ := exists_powerSeries_of_forall_coeff_neg_eq_zero _ hc
  obtain ⟨a', ha'⟩ := exists_powerSeries_of_forall_coeff_neg_eq_zero _ hb'
  refine ⟨a, a', ?_, ?_⟩
  · rw [ne_eq, map_residue_eq_zero_iff]
    intro h0
    apply hb
    have h1 : coeffMap (GaloisRep.ratLocalizedAtResidue p) (HahnSeries.single (N : ℤ) (1 : (↥(GaloisRep.ratLocalizedAt p))) * b) = 0 := by
      rw [← ha', coeffMap_ofPowerSeries, h0, map_zero]
    rw [map_mul, coeffMap_single, map_one] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (by rw [HahnSeries.single_eq_zero_iff]; exact one_ne_zero)
    · exact h2
  · have e1 : HahnSeries.ofPowerSeries ℤ ℚ (a'.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ)) =
        HahnSeries.single (N : ℤ) (1 : ℚ) * coeffMap (GaloisRep.ratLocalizedAt p).subtype b := by
      rw [← coeffMap_ofPowerSeries, ha', map_mul, coeffMap_single, map_one]; rfl
    have e2 : HahnSeries.ofPowerSeries ℤ ℚ (a.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ)) =
        HahnSeries.single (N : ℤ) (1 : ℚ) * coeffMap (GaloisRep.ratLocalizedAt p).subtype c := by
      rw [← coeffMap_ofPowerSeries, ha, map_mul, coeffMap_single, map_one]; rfl
    rw [e1, e2, mul_left_comm, h]

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra in"
theorem main :
    ∃ W₀ : ValuationSubring (↥(qExpFunctionFieldC ℚ Γ)),
      (∀ x : (↥(qExpFunctionFieldC ℚ Γ)), x ∈ W₀ ↔
        ∃ a a' : PowerSeries (↥(GaloisRep.ratLocalizedAt p)), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
          (x : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
            HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) ∧
      (∀ a : (↥(GaloisRep.ratLocalizedAt p)), algebraMap (↥(GaloisRep.ratLocalizedAt p)) (↥(qExpFunctionFieldC ℚ Γ)) a ∈ W₀) ∧
      (∀ a ∈ Ideal.span {((p : ℕ) : (↥(GaloisRep.ratLocalizedAt p)))}, algebraMap (↥(GaloisRep.ratLocalizedAt p)) (↥(qExpFunctionFieldC ℚ Γ)) a ∈ W₀.nonunits) ∧
      (∀ Q : Polynomial (↥(GaloisRep.ratLocalizedAt p)), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt Γ hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt Γ hj) Q)⁻¹ ∈ W₀) ∧
      (∀ x : (↥(qExpFunctionFieldC ℚ Γ)), x ∈ W₀.nonunits → x * (algebraMap (↥(GaloisRep.ratLocalizedAt p)) (↥(qExpFunctionFieldC ℚ Γ)) ((p : ℕ) : (↥(GaloisRep.ratLocalizedAt p))))⁻¹ ∈ W₀) := by
  have hK : qExpFunctionFieldC ℚ Γ = laurentBaseChange ℚ (qExpFunctionFieldC ℚ Γ) :=
    (laurentBaseChange_qExpFunctionFieldC_eq ℚ Γ).symm
  have hj' : ((jAt Γ hj : (↥(qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℚ) = coeffEmb ℚ jq := by rw [coeffEmb_rat, coe_jAt]; rfl
  haveI : IsFractionRing (↥(GaloisRep.ratLocalizedAt p)) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hst := IsScalarTower.of_algebraMap_eq (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ℚ) (A := ↥(qExpFunctionFieldC ℚ Γ)) (fun _ => rfl)
  obtain ⟨W₀, hmem, halg, hmax, hpoly, hnon⟩ :=
    @exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC Γ ℚ _ _ (qExpFunctionFieldC ℚ Γ) hK
      (↥(GaloisRep.ratLocalizedAt p)) _ _ _ _ _ _ hst (jAt Γ hj) hj' _
  refine ⟨W₀, fun x => ?_, halg, fun a ha => hmax a ?_, fun Q hQ => hpoly Q ?_, fun x hx => ?_⟩
  ·
    rw [hmem]
    constructor
    · rintro ⟨a, a', ha', h⟩
      exact ⟨a, a', fun h0 => ha' ((map_residue_eq_zero_iff p a').mpr h0), h⟩
    · rintro ⟨a, a', ha', h⟩
      exact ⟨a, a', fun h0 => ha' ((map_residue_eq_zero_iff p a').mp h0), h⟩
  · rw [maximalIdeal_eq]; exact ha
  · intro h0
    apply hQ
    ext n
    have hn := congrArg (fun P : Polynomial _ => P.coeff n) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hn ⊢
    exact (residue_eq_zero_iff' p _).mp hn
  ·
    have hxW : x ∈ W₀ := W₀.nonunits_subset hx
    obtain ⟨a, a', ha', h⟩ := (hmem x).mp hxW
    have ha0 : a.map (IsLocalRing.residue (↥(GaloisRep.ratLocalizedAt p))) = 0 := (hnon x a a' ha' h).mp hx
    have hcoef : ∀ n, ∃ s : (↥(GaloisRep.ratLocalizedAt p)), PowerSeries.coeff n a = p * s := fun n => by
      have hn := congrArg (PowerSeries.coeff n) ha0
      rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff, maximalIdeal_eq, Ideal.mem_span_singleton] at hn
      exact hn
    choose s hs using hcoef
    set a₁ : PowerSeries (↥(GaloisRep.ratLocalizedAt p)) := PowerSeries.mk s with ha₁
    have haa : a = (p : PowerSeries (↥(GaloisRep.ratLocalizedAt p))) * a₁ := by
      ext n
      rw [← map_natCast (PowerSeries.C (R := ↥(GaloisRep.ratLocalizedAt p))) p, PowerSeries.coeff_C_mul, ha₁,
        PowerSeries.coeff_mk, hs]
    rw [hmem]
    refine ⟨a₁, a', ha', ?_⟩
    have hp0 : (p : ↥(qExpFunctionFieldC ℚ Γ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    have hpa : HahnSeries.ofPowerSeries ℤ ℚ (a.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ)) =
        ((p : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) *
          HahnSeries.ofPowerSeries ℤ ℚ (a₁.map (algebraMap (↥(GaloisRep.ratLocalizedAt p)) ℚ)) := by
      rw [haa, map_mul, map_natCast, map_mul, map_natCast]
      push_cast
      rfl
    have halgp : (algebraMap (↥(GaloisRep.ratLocalizedAt p)) (↥(qExpFunctionFieldC ℚ Γ)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) =
        (p : ↥(qExpFunctionFieldC ℚ Γ)) := map_natCast _ p
    rw [halgp]
    push_cast
    have hpL : ((p : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ≠ 0 := by exact_mod_cast hp0
    rw [mul_right_comm, h, hpa, mul_right_comm]
    have hpL' : ((p : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * (((p : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ))⁻¹ = 1 :=
      mul_inv_cancel₀ hpL
    push_cast at hpL' ⊢
    rw [hpL', one_mul]

end Main

end ModularCurve.GaussExistsAlpha
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.ModularCurve.GaussExistsAlpha"
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.ModularCurve P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.ModularCurve.GaussExistsAlpha"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC.ModularCurve ModularCurve.XHDRLevel in
theorem solution
    (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ),

      (∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) ∧

      (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) a ∈ W₀) ∧
      (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))},
        algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) a ∈ W₀.nonunits) ∧

      (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt Γ hj) Q ∈ W₀ ∧ (Polynomial.aeval (jAt Γ hj) Q)⁻¹ ∈ W₀) ∧

      (∀ x : ↥(qExpFunctionFieldC ℚ Γ), x ∈ W₀.nonunits →
        x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ)
          ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ W₀) := by
  have hA : (DivisionRing.toRatAlgebra : Algebra ℚ ↥(qExpFunctionFieldC ℚ Γ)) =
      instAlgebraIntermediateFieldLaurent (qExpFunctionFieldC ℚ Γ) :=
    Algebra.algebra_ext _ _ (fun r => congrFun (congrArg DFunLike.coe (RingHom.ext_rat _ _)) r)
  have h := ModularCurve.GaussExistsAlpha.main p Γ hj
  rw [← hA] at h
  exact h

end S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC (solution)
