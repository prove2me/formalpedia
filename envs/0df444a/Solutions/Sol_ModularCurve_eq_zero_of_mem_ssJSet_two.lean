-- Prove2me | solution 1 for ModularCurve.eq_zero_of_mem_ssJSet_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4aa4632e-42ad-54b9-8678-6aea32a793dd

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_mem_ssJSet_two

set_option autoImplicit false

open ModularCurve WeierstrassCurve

namespace GaussPencil
namespace SS

theorem two_eq_zero (k : Type*) [Ring k] [CharP k 2] : (2 : k) = 0 := by
  simpa using CharP.cast_eq_zero k 2

theorem cast1728_eq_zero_of_two (k : Type*) [Ring k] [CharP k 2] : (1728 : k) = 0 := by
  rw [show (1728 : k) = 2 * 864 by norm_num, two_eq_zero k, zero_mul]

theorem exists_two_torsion_char_two {k : Type*} [Field k] [CharP k 2] [DecidableEq k]
    (a : k) (h0 : a ≠ 0) (ha4 : a ^ 4 = a) :
    ∃ P : (ofJNe0Or1728 a).toAffine.Point, P ≠ 0 ∧ 2 • P = 0 := by
  have h1728 : (1728 : k) = 0 := cast1728_eq_zero_of_two k
  have ha3 : a ^ 3 = 1 := by
    have : a * (a ^ 3 - 1) = 0 := by rw [mul_sub, mul_one, ← pow_succ', ha4, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h
  have hneg : ∀ x : k, -x = x := fun x => CharTwo.neg_eq x

  have heq : (ofJNe0Or1728 a).toAffine.Equation 0 a := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [ofJNe0Or1728, h1728, sub_zero]
    have : a ^ 5 = a ^ 2 := by rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, ha3, one_mul]
    rw [this]
    linear_combination a ^ 2 * two_eq_zero k
  haveI : Fact (IsUnit a) := ⟨isUnit_iff_ne_zero.mpr h0⟩
  haveI : Fact (IsUnit (a - 1728)) := ⟨by rw [h1728, sub_zero]; exact isUnit_iff_ne_zero.mpr h0⟩
  have hns : (ofJNe0Or1728 a).toAffine.Nonsingular 0 a :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular (W := ofJNe0Or1728 a)).mp heq
  refine ⟨WeierstrassCurve.Affine.Point.some _ _ hns, WeierstrassCurve.Affine.Point.some_ne_zero hns, ?_⟩
  have hy : a = (ofJNe0Or1728 a).toAffine.negY 0 a := by
    simp only [WeierstrassCurve.Affine.negY, ofJNe0Or1728, mul_zero, sub_zero]
    exact (hneg a).symm
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy

end GaussPencil.SS

theorem solution
    {k : Type*} [Field k] [CharP k 2] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 2 k) (ha2 : a ^ (2 ^ 2) = a) : a = 0 := by
  by_contra h0
  haveI : Fact (IsUnit a) := ⟨isUnit_iff_ne_zero.mpr h0⟩
  haveI : Fact (IsUnit (a - 1728)) :=
    ⟨by rw [GaussPencil.SS.cast1728_eq_zero_of_two k, sub_zero]; exact isUnit_iff_ne_zero.mpr h0⟩
  obtain ⟨P, hP0, hP2⟩ := GaussPencil.SS.exists_two_torsion_char_two a h0 (by simpa using ha2)
  exact hP0 (ha (ofJNe0Or1728 a) (ofJNe0Or1728_j a) P hP2)

end S_ModularCurve_eq_zero_of_mem_ssJSet_two
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_mem_ssJSet_two (solution)
