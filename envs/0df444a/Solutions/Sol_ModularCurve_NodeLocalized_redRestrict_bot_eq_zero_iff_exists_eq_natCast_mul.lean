-- Prove2me | solution 1 for ModularCurve.NodeLocalized.redRestrict_bot_eq_zero_iff_exists_eq_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/dd9c69e8-f2eb-5e9b-be30-e1f99f256c24

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_redRestrict_bot_eq_zero_iff_exists_eq_natCast_mul
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (c : ↥(coeffSubring A ⊥)) :
    redRestrict red ⊥ c = 0 ↔ ∃ d, c = ((q : ℕ) : ↥(coeffSubring A ⊥)) * d := by
  classical
  have hqP : q.Prime := Fact.out
  constructor
  · intro hc

    have hcK : ((c : ↥(coeffSubring A ⊥)) : AlgebraicClosure ℚ) ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
      (Subring.mem_inf.mp c.2).2
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hcK
    have hcA : ((c : ↥(coeffSubring A ⊥)) : AlgebraicClosure ℚ) ∈ A := (Subring.mem_inf.mp c.2).1

    have hintA : ∀ m : ℤ, ((m : AlgebraicClosure ℚ)) ∈ A := fun m => intCast_mem A m
    have hred_int : ∀ m : ℤ, red ⟨(m : AlgebraicClosure ℚ), hintA m⟩ = (m : k) := by
      intro m
      have e : (⟨(m : AlgebraicClosure ℚ), hintA m⟩ : A) = (m : A) := Subtype.ext (by push_cast; rfl)
      rw [e, map_intCast]
    have hunit_int : ∀ m : ℤ, ¬ (q : ℤ) ∣ m → IsUnit (⟨(m : AlgebraicClosure ℚ), hintA m⟩ : A) := by
      intro m hm
      by_contra hnu
      have hmem : (⟨(m : AlgebraicClosure ℚ), hintA m⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h0 : (m : k) = 0 := by rw [← hred_int m]; exact (hker _).mpr hmem
      exact hm ((CharP.intCast_eq_zero_iff k q m).mp h0)

    set cA : A := ⟨_, hcA⟩ with hcA_def
    have hc𝔪 : cA ∈ IsLocalRing.maximalIdeal A := by
      apply (hker cA).mp
      exact hc

    have hden0 : ((r.den : ℤ) : AlgebraicClosure ℚ) ≠ 0 := by
      exact_mod_cast r.den_nz
    have hcnum : ((c : ↥(coeffSubring A ⊥)) : AlgebraicClosure ℚ) * ((r.den : ℤ) : AlgebraicClosure ℚ)
        = ((r.num : ℤ) : AlgebraicClosure ℚ) := by
      rw [← hr, eq_div_iff hden0 |>.mp]
      rw [show (algebraMap ℚ (AlgebraicClosure ℚ)) r = (r : AlgebraicClosure ℚ) from rfl]
      push_cast
      exact (Rat.cast_def r)

    have hnden : ¬ (q : ℤ) ∣ (r.den : ℤ) := by
      intro hq_den
      have hnum_unit : IsUnit (⟨((r.num : ℤ) : AlgebraicClosure ℚ), hintA r.num⟩ : A) := by
        apply hunit_int
        intro hq_num
        have h1 : (q : ℕ) ∣ Nat.gcd r.num.natAbs r.den :=
          Nat.dvd_gcd (Int.natCast_dvd.mp hq_num) (Int.natCast_dvd_natCast.mp hq_den)
        rw [r.reduced] at h1
        exact hqP.one_lt.ne' (Nat.dvd_one.mp h1)
      have hnum𝔪 : (⟨((r.num : ℤ) : AlgebraicClosure ℚ), hintA r.num⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
        have e : (⟨((r.num : ℤ) : AlgebraicClosure ℚ), hintA r.num⟩ : A) = cA * ⟨((r.den : ℤ) : AlgebraicClosure ℚ), hintA r.den⟩ :=
          Subtype.ext hcnum.symm
        rw [e]
        exact Ideal.mul_mem_right _ _ hc𝔪
      exact (IsLocalRing.mem_maximalIdeal _).mp hnum𝔪 hnum_unit

    have hden_unit : IsUnit (⟨((r.den : ℤ) : AlgebraicClosure ℚ), hintA r.den⟩ : A) := hunit_int _ hnden
    have hqnum : (q : ℤ) ∣ r.num := by
      have hnum𝔪 : (⟨((r.num : ℤ) : AlgebraicClosure ℚ), hintA r.num⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
        have e : (⟨((r.num : ℤ) : AlgebraicClosure ℚ), hintA r.num⟩ : A) = cA * ⟨((r.den : ℤ) : AlgebraicClosure ℚ), hintA r.den⟩ :=
          Subtype.ext hcnum.symm
        rw [e]
        exact Ideal.mul_mem_right _ _ hc𝔪
      have h0 : ((r.num : ℤ) : k) = 0 := by rw [← hred_int]; exact (hker _).mpr hnum𝔪
      exact (CharP.intCast_eq_zero_iff k q _).mp h0
    obtain ⟨n', hn'⟩ := hqnum

    obtain ⟨v, hv⟩ := hden_unit
    have hvinv : (((v⁻¹ : (↥A)ˣ) : A) : AlgebraicClosure ℚ) = (((r.den : ℤ) : AlgebraicClosure ℚ))⁻¹ := by
      have h1 : (((v : A) : AlgebraicClosure ℚ)) * (((v⁻¹ : (↥A)ˣ) : A) : AlgebraicClosure ℚ) = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
      rw [hv] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hdA : ((n' : AlgebraicClosure ℚ)) * (((r.den : ℤ) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
      rw [← hvinv]
      exact mul_mem (hintA n') (SetLike.coe_mem _)
    have hdK : ((n' : AlgebraicClosure ℚ)) * (((r.den : ℤ) : AlgebraicClosure ℚ))⁻¹ ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
      refine IntermediateField.mem_bot.mpr ⟨(n' : ℚ) / (r.den : ℚ), ?_⟩
      rw [show (algebraMap ℚ (AlgebraicClosure ℚ)) ((n' : ℚ) / (r.den : ℚ)) = (((n' : ℚ) / (r.den : ℚ) : ℚ) : AlgebraicClosure ℚ) from rfl]
      push_cast
      rw [div_eq_mul_inv]
    refine ⟨⟨_, Subring.mem_inf.mpr ⟨hdA, hdK⟩⟩, Subtype.ext ?_⟩
    show ((c : ↥(coeffSubring A ⊥)) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) * (((n' : AlgebraicClosure ℚ)) * (((r.den : ℤ) : AlgebraicClosure ℚ))⁻¹)
    rw [← mul_assoc, eq_mul_inv_iff_mul_eq₀ hden0, hcnum, hn']
    push_cast
    ring
  · rintro ⟨d, rfl⟩
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

end S_ModularCurve_NodeLocalized_redRestrict_bot_eq_zero_iff_exists_eq_natCast_mul
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_redRestrict_bot_eq_zero_iff_exists_eq_natCast_mul (solution)
