-- Prove2me | solution 1 for MazurTransfer.mixed_inverse_parameter_reciprocal_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-15T05:36:35.055694+00:00
-- url     : https://prove2.me/submissions/1a5d34f2-8f16-4516-b243-f632e58f68c5

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: integral reciprocal recovery from the localized mixed
inverse-parameter relations. Named downstream consumer: the actual positive
infinity chart map of the second dyadic finite curve chart.
-/
import Mathlib
noncomputable section
theorem solution
    {A : Type*} [CommRing A] (s a b h l u v : A)
    (hh : h = l - a ^ 2) (hl : l = 1 - s - b)
    (hab : a * b = s * l) (hb : b ^ 2 * h = a * l ^ 2)
    (hu : h * u = 1) (hv : l * v = 1) :
    let z := b * v
    (z * a = s) ∧ (z ^ 2 * h = a) ∧ (z ^ 3 * h = s) ∧
    (u ^ 2 - (1 + z + z ^ 3) * u - z ^ 4 * (1 + z) = 0) ∧
    ((u - (1 + z + z ^ 3)) ^ 2 + (1 + z + z ^ 3) * (u - (1 + z + z ^ 3)) -
      (z ^ 4 + z ^ 5) = 0)  := by
  let z := b * v
  have hunit : IsUnit h := isUnit_iff_exists_inv.mpr ⟨u,hu⟩
  have lunit : IsUnit l := isUnit_iff_exists_inv.mpr ⟨v,hv⟩
  have hz : z * l = b := by
    dsimp only [z]
    linear_combination b * hv
  have hza : z * a = s := by
    apply lunit.mul_right_inj.mp
    linear_combination a * hz + hab
  have hz2 : z ^ 2 * h = a := by
    apply (lunit.pow 2).mul_right_inj.mp
    linear_combination hb + h * (z * l + b) * hz
  have hz3 : z ^ 3 * h = s := by
    linear_combination z * hz2 + hza
  have hz4 : z ^ 4 * h ^ 2 = a ^ 2 := by
    linear_combination (z ^ 2 * h + a) * hz2
  have hp : (1 + z + z ^ 3) * h + z ^ 4 * (1 + z) * h ^ 2 = 1 := by
    linear_combination hz + hz3 + (1 + z) * hz4 + (1 + z) * hh + hl
  have he : u ^ 2 - (1 + z + z ^ 3) * u - z ^ 4 * (1 + z) = 0 := by
    apply (hunit.pow 2).mul_right_inj.mp
    linear_combination (h * u + 1 - (1 + z + z ^ 3) * h) * hu - hp
  refine ⟨hza,hz2,hz3,he,?_⟩
  linear_combination he
#print axioms solution
