-- Prove2me | solution 1 for MazurProof.N13GoodModelTwo.affineEquation_iff_fixed
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:29:20.375662+00:00
-- url     : https://prove2.me/submissions/58a32538-bfa1-4da2-8431-7905423a1051

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13GoodModelTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodModelTwo =====
section
/-!
# A good characteristic-two model of `X₁(13)`

The completed-square sextic is not the model to reduce modulo two.  This file
uses the generalized hyperelliptic equation

`y² + (x³+x+1)y = x⁵+x⁴`.

Over the rationals, completing the square gives the existing N13 sextic.
In characteristic two, the affine chart and the chart at infinity both have
nonzero derivative in the second coordinate.  The `F₂`- and `F₄`-point
counts are obtained from Frobenius and the Artin--Schreier map, not by
enumerating field elements.
-/
namespace MazurProof.N13GoodModelTwo
noncomputable section
open scoped CharTwo
open Polynomial
universe u
variable {R : Type u} [CommRing R]
/-! ## The two charts of the weighted projective completion -/
/-! ## Structural characteristic-two point classification -/
variable {K : Type u} [Field K] [CharP K 2]
/-- In a field with four-power Frobenius, an affine point has both
coordinates in the prime subfield.  The non-prime-field branch is excluded
by the Artin--Schreier identity, not by a finite table. -/
theorem affineEquation_iff_fixed
    (hfour : ∀ z : K, z ^ 4 = z) (x y : K) :
    AffineEquation x y ↔ x ^ 2 = x ∧ y ^ 2 = y := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  constructor
  · intro hp
    have hidem : (x ^ 2 + x) ^ 2 = x ^ 2 + x := by
      linear_combination hfour x + x ^ 3 * htwo
    have hcases : x ^ 2 + x = 0 ∨ x ^ 2 + x = 1 := by
      have hfac : (x ^ 2 + x) * ((x ^ 2 + x) - 1) = 0 := by
        calc
          (x ^ 2 + x) * ((x ^ 2 + x) - 1) =
              (x ^ 2 + x) ^ 2 - (x ^ 2 + x) := by ring
          _ = 0 := sub_eq_zero.mpr hidem
      rcases mul_eq_zero.mp hfac with hzero | hone
      · exact Or.inl hzero
      · exact Or.inr (sub_eq_zero.mp hone)
    rcases hcases with hprime | hnonprime
    · have hx : x ^ 2 = x := by
        linear_combination hprime - x * htwo
      have hx3 : x ^ 3 = x := by
        calc
          x ^ 3 = x * x ^ 2 := by ring
          _ = x * x := by rw [hx]
          _ = x := by simpa [pow_two] using hx
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x := by simpa [pow_two] using hx
      have hh : h x = 1 := by
        simp only [h]
        linear_combination hx3 + x * htwo
      have hrhs : rhs x = 0 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + x * htwo
      have hy : y ^ 2 = y := by
        unfold AffineEquation at hp
        rw [hh, hrhs] at hp
        linear_combination hp - y * htwo
      exact ⟨hx, hy⟩
    · have hx3 : x ^ 3 = 1 := by
        linear_combination x * hnonprime - hnonprime + (x - 1) * htwo
      have hx4 : x ^ 4 = x := hfour x
      have hx5 : x ^ 5 = x ^ 2 := by
        calc
          x ^ 5 = x * x ^ 4 := by ring
          _ = x * x := by rw [hx4]
          _ = x ^ 2 := by ring
      have hh : h x = x := by
        simp only [h]
        linear_combination hx3 + htwo
      have hrhs : rhs x = 1 := by
        simp only [rhs]
        linear_combination hx5 + hx4 + hnonprime
      have hp' : y ^ 2 + x * y = 1 := by
        simpa [AffineEquation, hh, hrhs] using hp
      let t : K := y * x ^ 2
      have ht : t ^ 2 + t = x := by
        have hx4' : x ^ 4 = x := hfour x
        calc
          t ^ 2 + t = y ^ 2 * x ^ 4 + y * x ^ 2 := by
            simp only [t]
            ring
          _ = y ^ 2 * x + y * x ^ 2 := by rw [hx4']
          _ = x * (y ^ 2 + x * y) := by ring
          _ = x := by rw [hp']; ring
      have htFixed : (t ^ 2 + t) ^ 2 = t ^ 2 + t := by
        linear_combination hfour t + t ^ 3 * htwo
      rw [ht] at htFixed
      have hsumzero : x ^ 2 + x = 0 := by
        linear_combination htFixed + x * htwo
      have hzeroone : (0 : K) = 1 := hsumzero.symm.trans hnonprime
      exact (zero_ne_one hzeroone).elim
  · rintro ⟨hx, hy⟩
    have hx3 : x ^ 3 = x := by
      calc
        x ^ 3 = x * x ^ 2 := by ring
        _ = x * x := by rw [hx]
        _ = x := by simpa [pow_two] using hx
    have hx4 : x ^ 4 = x := hfour x
    have hx5 : x ^ 5 = x := by
      calc
        x ^ 5 = x * x ^ 4 := by ring
        _ = x * x := by rw [hx4]
        _ = x := by simpa [pow_two] using hx
    have hh : h x = 1 := by
      simp only [h]
      linear_combination hx3 + x * htwo
    have hrhs : rhs x = 0 := by
      simp only [rhs]
      linear_combination hx5 + hx4 + x * htwo
    unfold AffineEquation
    rw [hh, hrhs, hy]
    linear_combination y * htwo
/-! ## The fields `F₂` and `F₄` -/
attribute [local instance] MazurProof.N13GoodModelTwo.instFintypeF4
end
end MazurProof.N13GoodModelTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodModelTwo.affineEquation_iff_fixed := @MazurProof.N13GoodModelTwo.affineEquation_iff_fixed
