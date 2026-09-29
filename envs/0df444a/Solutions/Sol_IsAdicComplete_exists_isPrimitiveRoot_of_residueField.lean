-- Prove2me | solution 1 for IsAdicComplete.exists_isPrimitiveRoot_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/65d16307-627a-5dd3-a030-95884c10fd92

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdicComplete_exists_isPrimitiveRoot_of_residueField

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

theorem solution
    {W : Type*} [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hk : ∃ ζ₀ : IsLocalRing.ResidueField W, IsPrimitiveRoot ζ₀ n) :
    ∃ ζ : W, IsPrimitiveRoot ζ n := by
  classical
  obtain ⟨ζ₀, hζ₀⟩ := hk
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ζ₀
  set f : Polynomial W := Polynomial.X ^ n - Polynomial.C 1 with hf
  have hmonic : f.Monic := Polynomial.monic_X_pow_sub_C (1 : W) hn.ne'
  have heval : ∀ a : W, f.eval a = a ^ n - 1 := fun a => by
    simp [hf]
  have hderiv_eval : f.derivative.eval a₀ = (n : W) * a₀ ^ (n - 1) := by
    simp [hf, Polynomial.derivative_X_pow]

  have hroot : f.eval a₀ ∈ IsLocalRing.maximalIdeal W := by
    rw [← IsLocalRing.residue_eq_zero_iff, heval, map_sub, map_pow, ha₀, hζ₀.pow_eq_one, map_one, sub_self]

  have hunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal W) (f.derivative.eval a₀)) := by
    show IsUnit (IsLocalRing.residue W (f.derivative.eval a₀))
    rw [hderiv_eval, map_mul, map_pow, ha₀]
    exact (hnW.map (IsLocalRing.residue W)).mul ((hζ₀.isUnit hn.ne').pow (n - 1))

  obtain ⟨a, ha, hamem⟩ := HenselianRing.is_henselian f hmonic a₀ hroot hunit
  have han : a ^ n = 1 := by
    have h := ha.eq_zero
    rwa [heval, sub_eq_zero] at h
  have hres : IsLocalRing.residue W a = ζ₀ := by
    rw [← ha₀]
    exact (Ideal.Quotient.eq).2 hamem
  refine ⟨a, ⟨han, fun l hl => hζ₀.dvd_of_pow_eq_one l ?_⟩⟩
  rw [← hres, ← map_pow, hl, map_one]

end S_IsAdicComplete_exists_isPrimitiveRoot_of_residueField
end P2MW
export P2MW.S_IsAdicComplete_exists_isPrimitiveRoot_of_residueField (solution)
