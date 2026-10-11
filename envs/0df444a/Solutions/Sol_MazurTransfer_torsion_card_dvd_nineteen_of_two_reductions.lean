-- Prove2me | solution 1 for MazurTransfer.torsion_card_dvd_nineteen_of_two_reductions
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T12:52:35.2072+00:00
-- url     : https://prove2.me/submissions/bb0b3ae0-86f7-4111-99c3-5091074ad4ff

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an abstract torsion bound from two reduction homomorphisms
with nineteen-element targets and prime-to-3/prime-to-5 kernel detection.
Named downstream consumer: the same integral order-13 rational Picard family.
-/
import Mathlib

namespace MazurTransfer.PublicTwoReductionTorsionBoundProof
variable {G A B : Type*} [CommGroup G] [Group A] [Group B]
variable (r3 : G →* A) (r5 : G →* B)
variable (hA : Nat.card A = 19) (hB : Nat.card B = 19)
variable (h3 : ∀ (m : ℕ), ¬ 3 ∣ m → ∀ x : G, x ^ m = 1 → r3 x = 1 → x = 1)
variable (h5 : ∀ (m : ℕ), ¬ 5 ∣ m → ∀ x : G, x ^ m = 1 → r5 x = 1 → x = 1)

include r5 hB h5 in
theorem three_not_dvd_torsion_order (x : G) (hx : IsOfFinOrder x) : ¬ 3 ∣ orderOf x := by
  intro hd
  let y := x ^ (orderOf x / 3)
  have hyorder : orderOf y = 3 := orderOf_pow_orderOf_div (orderOf_ne_zero_iff.mpr hx) hd
  have hy3 : y ^ 3 = 1 := by rw [← hyorder]; exact pow_orderOf_eq_one y
  have hr3 : (r5 y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hr19 : (r5 y) ^ 19 = 1 := by rw [← hB]; exact pow_card_eq_one'
  have hd1 : orderOf (r5 y) ∣ 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hr3) (orderOf_dvd_of_pow_eq_one hr19)
    simpa using h
  have hyone : y = 1 := h5 3 (by decide) y hy3 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1))
  have hc : (3 : ℕ) = 1 := by simpa only [orderOf_one] using hyorder.symm.trans (congrArg orderOf hyone)
  omega

include r3 r5 hA hB h3 h5 in
theorem torsion_pow_nineteen (x : G) (hx : IsOfFinOrder x) : x ^ 19 = 1 := by
  have hn : ¬ 3 ∣ orderOf x := three_not_dvd_torsion_order r5 hB h5 x hx
  have hp : (x ^ 19) ^ orderOf x = 1 := by rw [pow_right_comm, pow_orderOf_eq_one, one_pow]
  have hr : r3 (x ^ 19) = 1 := by rw [map_pow, ← hA]; exact pow_card_eq_one'
  exact h3 (orderOf x) hn (x ^ 19) hp hr

include r3 r5 hA hB h3 h5 in
theorem torsion_reduction_injective :
    Function.Injective (r3.comp (CommGroup.torsion G).subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  apply Subtype.ext
  exact h3 19 (by decide) x.val
    (torsion_pow_nineteen r3 r5 hA hB h3 h5 x.val x.property) hx

include r3 r5 hA hB h3 h5 in
theorem torsion_card_dvd_nineteen : Nat.card (CommGroup.torsion G) ∣ 19 := by
  rw [← hA]
  exact Subgroup.card_dvd_of_injective (r3.comp (CommGroup.torsion G).subtype)
    (torsion_reduction_injective r3 r5 hA hB h3 h5)

include r3 r5 hA hB h3 h5 in
theorem torsion_finite [Finite A] : Finite (CommGroup.torsion G) :=
  Finite.of_injective (r3.comp (CommGroup.torsion G).subtype)
    (torsion_reduction_injective r3 r5 hA hB h3 h5)

end MazurTransfer.PublicTwoReductionTorsionBoundProof

theorem solution
    {G A B : Type*} [CommGroup G] [Group A] [Group B]
    (r3 : G →* A) (r5 : G →* B)
    (hA : Nat.card A = 19) (hB : Nat.card B = 19)
    (h3 : ∀ (m : ℕ), ¬ 3 ∣ m → ∀ x : G, x ^ m = 1 → r3 x = 1 → x = 1)
    (h5 : ∀ (m : ℕ), ¬ 5 ∣ m → ∀ x : G, x ^ m = 1 → r5 x = 1 → x = 1) :
    Nat.card (CommGroup.torsion G) ∣ 19 := by
  exact MazurTransfer.PublicTwoReductionTorsionBoundProof.torsion_card_dvd_nineteen
    r3 r5 hA hB h3 h5

#print axioms solution
