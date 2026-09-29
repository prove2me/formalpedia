-- Prove2me | solution 1 for ModularCurve.FullLevel.val_neg_natCast_pos_and_min_ne_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/73c2009b-3145-5562-ab9a-4bc40a467d76

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_val_neg_natCast_pos_and_min_ne_of_isCoprime

set_option autoImplicit false

namespace ArithAux

theorem skeleton (n q J₁ J₂ : ℕ) (hn : n % 2 = 1) (h3 : 3 * q ≤ n) (hq : 0 < q) (hJ₁ : J₁ = n - q)
    (hJ₂pos : 0 < J₂) (hJ₂lt : J₂ < n) (hJ₂q : J₂ ≠ q) (hJ₂nq : J₂ ≠ n - q) :
    0 < J₁ ∧ J₁ < n ∧ 0 < J₂ ∧ J₂ < n ∧ 2 * J₁ ≠ n ∧ 2 * J₂ ≠ n ∧ min J₁ (n - J₁) ≠ min J₂ (n - J₂) := by
  omega

end ArithAux

theorem solution
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hq : 5 ≤ q) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (g : ℤ) (hg : IsCoprime g q) :
    0 < (-(q : ZMod (q * ℓ))).val ∧ (-(q : ZMod (q * ℓ))).val < q * ℓ ∧
    0 < (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val ∧
    (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val < q * ℓ ∧
    2 * (-(q : ZMod (q * ℓ))).val ≠ q * ℓ ∧
    2 * (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val ≠ q * ℓ ∧
    min (-(q : ZMod (q * ℓ))).val (q * ℓ - (-(q : ZMod (q * ℓ))).val) ≠
      min (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val
        (q * ℓ - (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val) := by
  have hqP : q.Prime := Fact.out
  have hℓP : ℓ.Prime := Fact.out
  have hq0 : 0 < q := hqP.pos
  have hℓ2 : 2 ≤ ℓ := hℓP.two_le
  have h3 : 3 * q ≤ q * ℓ := by nlinarith
  have hqn : q < q * ℓ := by nlinarith
  haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqP.ne_zero hℓP.ne_zero⟩

  have hodd : (q * ℓ) % 2 = 1 :=
    Nat.odd_iff.mp ((hqP.odd_of_ne_two (by omega)).mul (hℓP.odd_of_ne_two (by omega)))

  have hqval : (q : ZMod (q * ℓ)).val = q := ZMod.val_natCast_of_lt hqn
  have hq0' : (q : ZMod (q * ℓ)) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [hqval, ZMod.val_zero] at this
    omega
  have hJ₁ : (-(q : ZMod (q * ℓ))).val = q * ℓ - q := by
    rw [ZMod.neg_val, if_neg hq0', hqval]

  set x : ZMod (q * ℓ) := -(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ)) with hx
  let φ : ZMod (q * ℓ) →+* ZMod q := ZMod.castHom (dvd_mul_right q ℓ) (ZMod q)
  have hφq : φ (q : ZMod (q * ℓ)) = 0 := by rw [map_natCast, ZMod.natCast_self]
  have hgq : (g : ZMod q) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have hu : IsUnit (q : ℤ) := hg.isUnit_of_dvd' h dvd_rfl
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact hqP.one_lt.ne' hu
  have hℓq' : (ℓ : ZMod q) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (ZMod q) q] at h
    exact hℓq ((Nat.prime_dvd_prime_iff_eq hqP hℓP).mp h).symm
  have hφx : φ x ≠ 0 := by
    rw [hx, map_sub, map_neg, map_mul, hφq, map_intCast, map_natCast, neg_zero, zero_sub, neg_ne_zero]
    exact mul_ne_zero hgq hℓq'
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  have hxq : x ≠ (q : ZMod (q * ℓ)) := fun h => hφx (by rw [h, hφq])
  have hxnq : x ≠ -(q : ZMod (q * ℓ)) := fun h => hφx (by rw [h, map_neg, hφq, neg_zero])
  have hJ₂pos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx0 ((ZMod.val_eq_zero x).mp h))
  have hJ₂lt : x.val < q * ℓ := ZMod.val_lt x
  have hJ₂q : x.val ≠ q := by
    intro h
    apply hxq
    rw [← ZMod.natCast_zmod_val x, h]
  have hJ₂nq : x.val ≠ q * ℓ - q := by
    intro h
    apply hxnq
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_sub hqn.le, ZMod.natCast_self, zero_sub]
  exact ArithAux.skeleton (q * ℓ) q _ _ hodd h3 hq0 hJ₁ hJ₂pos hJ₂lt hJ₂q hJ₂nq

#print axioms solution

end S_ModularCurve_FullLevel_val_neg_natCast_pos_and_min_ne_of_isCoprime
end P2MW
export P2MW.S_ModularCurve_FullLevel_val_neg_natCast_pos_and_min_ne_of_isCoprime (solution)
