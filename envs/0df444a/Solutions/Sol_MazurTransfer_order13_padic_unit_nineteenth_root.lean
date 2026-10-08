-- Prove2me | solution 1 for MazurTransfer.order13_padic_unit_nineteenth_root
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T19:27:43.001895+00:00
-- url     : https://prove2.me/submissions/e504778b-58ad-423a-b9a7-1dbdcd86d8a3

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Local arithmetic component for the classical order-13 descent.
Design boundary: this concerns the actual unit group of the 13-adic integers.
The named downstream consumer `order13_padic_unit_no_cyclic_19_quotient` below
excludes its cyclic quotients of order 19. It does not assert a class-field
comparison, construct the Jacobian, or discharge the global point obstruction.
-/
import Mathlib

open Polynomial

namespace MazurTransfer

theorem order13_padic_unit_nineteenth_root [Fact (Nat.Prime 13)]
    (u : (ℤ_[13])ˣ) : ∃ v : (ℤ_[13])ˣ, v ^ 19 = u := by
  let a : ℤ_[13] := (u : ℤ_[13]) ^ 7
  let F : Polynomial ℤ_[13] := X ^ 19 - C (u : ℤ_[13])
  have ha : IsUnit a := (Units.isUnit u).pow 7
  have haNorm : ‖a‖ = 1 := PadicInt.isUnit_iff.mp ha
  have heval : F.aeval a = a ^ 19 - (u : ℤ_[13]) := by simp [F]
  have hderiv : F.derivative.aeval a = 19 * a ^ 18 := by simp [F] <;> norm_num
  have h19Norm : ‖(19 : ℤ_[13])‖ = 1 := by
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 13 19)
  have hderivNorm : ‖F.derivative.aeval a‖ = 1 := by
    rw [hderiv, norm_mul, norm_pow, h19Norm, haNorm]
    norm_num
  have hresidue : ∀ x : ZMod 13, x ^ 133 = x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hx12 : x ^ 12 = 1 := ZMod.pow_card_sub_one_eq_one hx
      calc
        x ^ 133 = (x ^ 12) ^ 11 * x := by ring
        _ = x := by rw [hx12]; simp
  have hevalResidue : PadicInt.toZMod (F.aeval a) = 0 := by
    rw [heval, map_sub, map_pow]
    simp only [a, map_pow, ← pow_mul]
    norm_num only [Nat.reduceMul]
    rw [hresidue, sub_self]
  have hevalNorm : ‖F.aeval a‖ < 1 := by
    have hmem : F.aeval a ∈ RingHom.ker (PadicInt.toZMod (p := 13)) := hevalResidue
    rw [PadicInt.ker_toZMod] at hmem
    rw [IsLocalRing.mem_maximalIdeal] at hmem
    exact PadicInt.mem_nonunits.mp hmem
  have hHensel : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    simpa only [hderivNorm, one_pow] using hevalNorm
  obtain ⟨z, hz, hnear, _, _⟩ := hensels_lemma hHensel
  have hzUnit : IsUnit z := by
    rw [hderivNorm] at hnear
    have hsum := PadicInt.norm_add_eq_max_of_ne
      (q := z - a) (r := a) (by rw [haNorm]; exact ne_of_lt hnear)
    rw [sub_add_cancel, haNorm, max_eq_right (le_of_lt hnear)] at hsum
    exact PadicInt.isUnit_iff.mpr hsum
  obtain ⟨v, hv⟩ := hzUnit
  refine ⟨v, Units.ext ?_⟩
  have hpow : z ^ 19 = (u : ℤ_[13]) := by
    have hz' : z ^ 19 - (u : ℤ_[13]) = 0 := by simpa [F] using hz
    exact sub_eq_zero.mp hz'
  simpa only [Units.val_pow_eq_pow_val, hv] using hpow

theorem order13_padic_unit_no_cyclic_19_quotient [Fact (Nat.Prime 13)]
    (f : (ℤ_[13])ˣ →* Multiplicative (ZMod 19)) : f = 1 := by
  ext u
  obtain ⟨v, rfl⟩ := order13_padic_unit_nineteenth_root u
  rw [map_pow]
  change Multiplicative.ofAdd (19 • Multiplicative.toAdd (f v)) = 1
  rw [ZModModule.char_nsmul_eq_zero 19]
  rfl

end MazurTransfer


theorem solution [Fact (Nat.Prime 13)] (u : (ℤ_[13])ˣ) :
    ∃ v : (ℤ_[13])ˣ, v ^ 19 = u :=
  MazurTransfer.order13_padic_unit_nineteenth_root u
