-- Prove2me | solution 1 for ModularCurve.mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/356b862a-7380-5e03-b7de-ea2146f912f0

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap

set_option autoImplicit false

open ModularCurve

namespace E142Bridge

open HahnSeries

theorem coeff_ofPowerSeries_of_neg {R : Type*} [CommSemiring R] (p : PowerSeries R) (n : ℤ) (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ R p).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  have : ((m : ℕ) : ℤ) = n := by simpa using hm
  omega

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (p : PowerSeries R) :
    coeffMap g (HahnSeries.ofPowerSeries ℤ R p) = HahnSeries.ofPowerSeries ℤ S (p.map g) := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [coeffMap_coeff, coeff_ofPowerSeries_of_neg _ _ hn, coeff_ofPowerSeries_of_neg _ _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g) :
    Function.Injective (coeffMap g) := by
  intro x y h
  ext n
  apply hg
  have := congrArg (fun z => HahnSeries.coeff z n) h
  simpa [coeffMap_coeff] using this

def inclA {k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)} (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (A₁ : ValuationSubring ↥K₁)
    (h : ∀ a : ↥A₁, ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A) : ↥A₁ →+* ↥A where
  toFun a := ⟨((a : ↥K₁) : AlgebraicClosure ℚ), h a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[scoped simp] theorem coe_inclA {k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)} (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (A₁ : ValuationSubring ↥K₁)
    (h : ∀ a : ↥A₁, ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A) (a : ↥A₁) :
    ((inclA K₁ A A₁ h a : ↥A) : AlgebraicClosure ℚ) = ((a : ↥K₁) : AlgebraicClosure ℚ) := rfl

end E142Bridge
p2m_reactivate "P2MW.S_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap.E142Bridge"

open E142Bridge

set_option maxHeartbeats 1600000 in
theorem solution
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    (K : IntermediateField ↥K₁ (LaurentSeries ↥K₁))

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A₁, y.map (IsLocalRing.residue ↥A₁) ≠ 0 ∧
      (f : LaurentSeries ↥K₁) * HahnSeries.ofPowerSeries ℤ ↥K₁ (y.map (algebraMap ↥A₁ ↥K₁))
        = HahnSeries.ofPowerSeries ℤ ↥K₁ (x.map (algebraMap ↥A₁ ↥K₁)))

    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (O : ValuationSubring ↥E)
    (hO : ∀ f : ↥E, f ∈ O ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (φ : ↥K →+* ↥E)
    (hφ : ∀ f : ↥K, ((φ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁)) :
    (∀ f : ↥K, f ∈ W₀ ↔ φ f ∈ O) ∧
    (∀ f : ↥K, (f : ↥K) ∈ W₀.nonunits ↔ (φ f : ↥E) ∈ O.nonunits) := by
  have hA₁A : ∀ a : ↥A₁, ((a : ↥K₁) : AlgebraicClosure ℚ) ∈ A := fun a => (hA₁ a).mp a.2

  have hunit : ∀ a : ↥A₁, IsLocalRing.residue ↥A₁ a ≠ 0 →
      IsLocalRing.residue ↥A (inclA K₁ A A₁ hA₁A a) ≠ 0 := by
    intro a ha h
    rw [IsLocalRing.residue_eq_zero_iff] at h
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff] at ha
    exact ha ((IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp h (hu.map (inclA K₁ A A₁ hA₁A)))

  have hnonunit : ∀ a : ↥A₁, IsLocalRing.residue ↥A₁ a = 0 →
      IsLocalRing.residue ↥A (inclA K₁ A A₁ hA₁A a) = 0 := by
    intro a ha
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff,
      ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at ha ⊢
    rw [coe_inclA]
    rcases ha with ha | ha
    · left; rw [ha]; simp
    · right
      intro hinv
      apply ha
      rw [hA₁]
      simpa using hinv

  have hlift : ∀ p : PowerSeries ↥A₁,
      coeffMap A.subtype (HahnSeries.ofPowerSeries ℤ ↥A (p.map (inclA K₁ A A₁ hA₁A))) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ))
        (HahnSeries.ofPowerSeries ℤ ↥K₁ (p.map (algebraMap ↥A₁ ↥K₁))) := by
    intro p
    have hmaps : (p.map (inclA K₁ A A₁ hA₁A)).map A.subtype =
        (p.map (algebraMap ↥A₁ ↥K₁)).map (algebraMap ↥K₁ (AlgebraicClosure ℚ)) := by
      ext n; simp only [PowerSeries.coeff_map]; rfl
    rw [coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, hmaps]
  have hlift_ne : ∀ p : PowerSeries ↥A₁, p.map (IsLocalRing.residue ↥A₁) ≠ 0 →
      coeffMap (IsLocalRing.residue ↥A) (HahnSeries.ofPowerSeries ℤ ↥A (p.map (inclA K₁ A A₁ hA₁A))) ≠ 0 := by
    intro p hp h
    apply hp
    ext m
    have hm := congrArg (fun z => HahnSeries.coeff z (m : ℤ)) h
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      HahnSeries.coeff_zero] at hm
    rw [PowerSeries.coeff_map, map_zero]
    by_contra hne
    exact hunit _ hne hm
  have hlift_zero : ∀ p : PowerSeries ↥A₁, p.map (IsLocalRing.residue ↥A₁) = 0 →
      coeffMap (IsLocalRing.residue ↥A) (HahnSeries.ofPowerSeries ℤ ↥A (p.map (inclA K₁ A A₁ hA₁A))) = 0 := by
    intro p hp
    ext n
    rw [coeffMap_coeff, HahnSeries.coeff_zero]
    rcases lt_or_ge n 0 with hn | hn
    · rw [coeff_ofPowerSeries_of_neg _ _ hn, map_zero]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
      apply hnonunit
      have := congrArg (fun z => PowerSeries.coeff m z) hp
      simp only [PowerSeries.coeff_map] at this
      exact this

  have hforward : ∀ f : ↥K, f ∈ W₀ → φ f ∈ O := by
    intro f hf
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ f).mp hf
    refine (hO _).mpr ⟨HahnSeries.ofPowerSeries ℤ ↥A (x.map (inclA K₁ A A₁ hA₁A)),
      HahnSeries.ofPowerSeries ℤ ↥A (y.map (inclA K₁ A A₁ hA₁A)), hlift_ne y hy, ?_⟩
    rw [hφ, hlift, hlift, ← map_mul, hxy]

  have hbackward : ∀ f : ↥K, φ f ∈ O → f ∈ W₀ := by
    intro f hφf
    rcases eq_or_ne f 0 with hf0 | hf0
    · rw [hf0]; exact zero_mem W₀
    rcases W₀.mem_or_inv_mem f with h | h
    · exact h
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ _).mp h
    have hfK : ((f : ↥K) : LaurentSeries ↥K₁) ≠ 0 := fun h0 => hf0 (Subtype.ext h0)
    have hinv : (((f⁻¹ : ↥K) : ↥K) : LaurentSeries ↥K₁) = ((f : ↥K) : LaurentSeries ↥K₁)⁻¹ := rfl
    rcases eq_or_ne (x.map (IsLocalRing.residue ↥A₁)) 0 with hx | hx
    ·
      exfalso
      obtain ⟨x₂, y₂, hy₂, h₂⟩ := (hO _).mp hφf
      have hF : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁) ≠ 0 := by
        intro h0
        apply hfK
        exact coeffMap_injective _ (algebraMap ↥K₁ (AlgebraicClosure ℚ)).injective (by rw [h0, map_zero])
      have hxy' : coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁)⁻¹ *
          coeffMap A.subtype (HahnSeries.ofPowerSeries ℤ ↥A (y.map (inclA K₁ A A₁ hA₁A))) =
          coeffMap A.subtype (HahnSeries.ofPowerSeries ℤ ↥A (x.map (inclA K₁ A A₁ hA₁A))) := by
        rw [hlift, hlift, ← map_mul, ← hinv, hxy]
      rw [map_inv₀] at hxy'
      rw [hφ] at h₂
      have hprod : coeffMap A.subtype (y₂ * HahnSeries.ofPowerSeries ℤ ↥A (y.map (inclA K₁ A A₁ hA₁A))) =
          coeffMap A.subtype (x₂ * HahnSeries.ofPowerSeries ℤ ↥A (x.map (inclA K₁ A A₁ hA₁A))) := by
        rw [map_mul, map_mul, ← h₂, ← hxy', mul_mul_mul_comm, mul_inv_cancel₀ hF, one_mul]
      have heq := coeffMap_injective _ (Subtype.coe_injective) hprod
      have := congrArg (coeffMap (IsLocalRing.residue ↥A)) heq
      rw [map_mul, map_mul, hlift_zero x hx, mul_zero] at this
      exact mul_ne_zero hy₂ (hlift_ne y hy) this
    ·
      refine (hW₀ f).mpr ⟨y, x, hx, ?_⟩
      rw [hinv] at hxy
      rw [← hxy, ← mul_assoc, mul_inv_cancel₀ hfK, one_mul]
  have h1 : ∀ f : ↥K, f ∈ W₀ ↔ φ f ∈ O := fun f => ⟨hforward f, hbackward f⟩
  refine ⟨h1, fun f => ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, ← h1,
    map_eq_zero_iff φ φ.injective]

end S_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
end P2MW
export P2MW.S_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap (solution)
