-- Prove2me | solution 1 for IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/85cc65e7-69e0-5ad1-893a-ac5058091f62

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible

set_option maxHeartbeats 4800000

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    (algebraMap R ℚ).range = GaloisRep.ratLocalizedAt p := by
  have hinj : Function.Injective (algebraMap R ℚ) := IsFractionRing.injective R ℚ
  have hp_not_unit : ¬ IsUnit (p : R) := hp.not_isUnit
  have hintR : ∀ n : ℤ, algebraMap R ℚ (n : R) = (n : ℚ) := fun n =>
    map_intCast (algebraMap R ℚ) n
  have hnatR : ∀ n : ℕ, algebraMap R ℚ (n : R) = (n : ℚ) := fun n =>
    map_natCast (algebraMap R ℚ) n

  have unit_of_coprime : ∀ n : ℕ, n.Coprime p → IsUnit (n : R) := by
    intro n hcop
    have h1 : IsCoprime (n : ℤ) (p : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hcop)
    obtain ⟨u, v, huv⟩ := h1
    have hR : (u : R) * (n : R) + (v : R) * (p : R) = 1 := by
      have := congrArg (fun z : ℤ => (z : R)) huv
      push_cast at this; exact_mod_cast this
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hR with h | h
    · exact isUnit_of_mul_isUnit_right h
    · exact absurd (isUnit_of_mul_isUnit_right h) hp_not_unit

  have den_mul : ∀ q : ℚ, (q.den : ℚ) * q = (q.num : ℚ) := fun q => by
    have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    rw [mul_comm, ← eq_div_iff hd]; exact (Rat.num_div_den q).symm
  apply le_antisymm
  ·
    rintro _ ⟨r, rfl⟩
    set q := algebraMap R ℚ r with hq_def
    show q.den.Coprime p
    by_contra hden
    have hpd : p ∣ q.den :=
      ((Fact.out : p.Prime).dvd_iff_not_coprime).mpr (fun h => hden h.symm)

    have hbr : (q.den : R) * r = (q.num : R) := by
      apply hinj
      rw [map_mul, hnatR, hintR, ← hq_def]
      exact den_mul q

    have hcop : IsCoprime (q.num : ℤ) (q.den : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast q.reduced)
    obtain ⟨x, y, hxy⟩ := hcop
    have hxyR : (x : R) * (q.num : R) + (y : R) * (q.den : R) = 1 := by
      have := congrArg (fun z : ℤ => (z : R)) hxy
      push_cast at this; exact_mod_cast this

    have hone : (q.den : R) * ((x : R) * r + (y : R)) = 1 := by
      rw [mul_add, ← mul_assoc, mul_comm (q.den : R) (x : R), mul_assoc, hbr]
      linear_combination hxyR
    have hden_unit : IsUnit (q.den : R) :=
      ⟨⟨_, _, hone, by rw [mul_comm]; exact hone⟩, rfl⟩

    obtain ⟨k, hk⟩ := hpd
    have : IsUnit (p : R) := by
      have : (q.den : R) = (p : R) * (k : R) := by
        rw [hk]; push_cast; ring
      rw [this] at hden_unit
      exact isUnit_of_mul_isUnit_left hden_unit
    exact hp_not_unit this
  ·
    intro q hq
    obtain ⟨u, hu⟩ := unit_of_coprime q.den hq
    refine ⟨(q.num : R) * (↑u⁻¹ : R), ?_⟩
    have huq : algebraMap R ℚ (↑u : R) = (q.den : ℚ) := by rw [hu]; exact hnatR q.den
    have huinv : algebraMap R ℚ (↑u⁻¹ : R) * (q.den : ℚ) = 1 := by
      rw [← huq, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    rw [map_mul, hintR]
    have h1 : algebraMap R ℚ (↑u⁻¹ : R) = (q.den : ℚ)⁻¹ :=
      (eq_inv_of_mul_eq_one_left huinv)
    rw [h1, ← div_eq_mul_inv]
    exact Rat.num_div_den q

end S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
end P2MW
export P2MW.S_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible (solution)
