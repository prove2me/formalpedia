-- Prove2me | solution 1 for Matrix.exists_det_map_eq_of_isUnit_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d974c450-357a-5126-8179-a5649e9cf2ce

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_det_map_eq_of_isUnit_of_ne

set_option autoImplicit false

theorem solution
    (ℓ q : ℕ) [Fact ℓ.Prime] [Fact q.Prime] (hℓq : ℓ ≠ q) (u : (ZMod ℓ)ˣ) (v : (ZMod q)ˣ) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det ∧
      ((g.det : ℤ) : ZMod ℓ) = (u : ZMod ℓ) ∧ ((g.det : ℤ) : ZMod q) = (v : ZMod q) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hco : Nat.Coprime ℓ q := (Nat.coprime_primes Fact.out Fact.out).mpr hℓq
  obtain ⟨d, hdℓ, hdq⟩ := Nat.chineseRemainder hco (u : ZMod ℓ).val (v : ZMod q).val
  have hdℓ' : (d : ZMod ℓ) = (u : ZMod ℓ) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hdℓ, ZMod.natCast_zmod_val]
  have hdq' : (d : ZMod q) = (v : ZMod q) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hdq, ZMod.natCast_zmod_val]
  have hcoℓ : Nat.Coprime d ℓ := by
    rw [Nat.coprime_iff_gcd_eq_one, hdℓ.gcd_eq]
    exact ZMod.val_coe_unit_coprime u
  have hcoq : Nat.Coprime d q := by
    rw [Nat.coprime_iff_gcd_eq_one, hdq.gcd_eq]
    exact ZMod.val_coe_unit_coprime v
  refine ⟨!![(d : ℤ), 0; 0, 1], ?_, ?_, ?_⟩
  · have hdet : (Matrix.map !![(d : ℤ), 0; 0, 1] (Int.castRingHom (ZMod (q * ℓ)))).det =
        ((d : ℕ) : ZMod (q * ℓ)) := by
      simp [Matrix.det_fin_two]
    rw [hdet, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.mul_right hcoq hcoℓ
  · simp [Matrix.det_fin_two, hdℓ']
  · simp [Matrix.det_fin_two, hdq']

end S_Matrix_exists_det_map_eq_of_isUnit_of_ne
end P2MW
export P2MW.S_Matrix_exists_det_map_eq_of_isUnit_of_ne (solution)
