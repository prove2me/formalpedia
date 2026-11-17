-- Prove2me | solution 1 for N25.canonicalChartPoint25_exists_minor_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:53.74557+00:00
-- url     : https://prove2.me/submissions/6ecdfcdc-893e-4b75-a874-e351b4acb438

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_normalized_projective_point_not_singular
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_normalized_projective_point_not_singular
import Theorems.Thm_N25_canonicalCubicGradient25_euler
import Theorems.Thm_N25_canonicalJacobianMinor25_eval
import Theorems.Thm_N25_canonicalQuadricGradient25_euler

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

end MazurProof.RationalPointsN25QuotientSmoothF3

namespace N25

open scoped BigOperators

private theorem minors_zero_of_complementary_columns {K : Type*} [CommRing K]
    (v q c : Fin 4 → K) (i : Fin 4) (hi : v i = 1)
    (hq : ∑ j : Fin 4, v j * q j = 0) (hc : ∑ j : Fin 4, v j * c j = 0)
    (h : ∀ j k : Fin 4, j ≠ i → k ≠ i → j < k → q j*c k-c j*q k = 0) :
    ∀ j k : Fin 4, q j*c k-c j*q k = 0 := by
  have hoff (j k : Fin 4) (hj : j ≠ i) (hk : k ≠ i) : q j*c k-c j*q k = 0 := by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact h j k hj hk hjk
    · ring
    · linear_combination -(h k j hk hj hkj)
  have hpivot (j : Fin 4) (hj : j ≠ i) : q i*c j-c i*q j = 0 := by
    have hsum : (∑ t : Fin 4, v t * (q t*c j-c t*q j)) = 0 := by
      calc
        _ = (∑ t : Fin 4, v t*q t)*c j-(∑ t : Fin 4, v t*c t)*q j := by
          simp only [Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro t _ <;> ring
        _ = 0 := by rw [hq, hc]; ring
    have heq : (∑ t : Fin 4, v t * (q t*c j-c t*q j)) =
        v i * (q i*c j-c i*q j) := by
      apply Finset.sum_eq_single i
      · intro t _ hti
        rw [hoff t j hti hj, mul_zero]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i))
    rw [heq, hi, one_mul] at hsum
    exact hsum
  intro j k
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k; ring
    · exact hpivot k hk
  · by_cases hk : k = i
    · subst k
      linear_combination -(hpivot j hj)
    · exact hoff j k hj hk

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

private theorem singular_two_scale {K : Type*} [Field K]
    (a : K) (P : Coordinates4 K) (h : MazurProof.RationalPointsN25QuotientSmoothF2.IsCanonicalSingular25CharTwo P) :
    MazurProof.RationalPointsN25QuotientSmoothF2.IsCanonicalSingular25CharTwo (scaleCoordinatesThree a P) := by
  rcases h with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
  have eqQ : MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo (scaleCoordinatesThree a P) =
      a^2 * MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo P := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo]
    ring
  have eqC : MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo (scaleCoordinatesThree a P) =
      a^3 * MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo P := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo]
    ring
  have eqxy : (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo (scaleCoordinatesThree a P)).xy =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo P).xy := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo]
    ring
  have eqxz : (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo (scaleCoordinatesThree a P)).xz =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo P).xz := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo]
    ring
  have eqxw : (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo (scaleCoordinatesThree a P)).xw =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo P).xw := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo]
    ring
  have eqyz : (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo (scaleCoordinatesThree a P)).yz =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo P).yz := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo]
    ring
  have eqyw : (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo (scaleCoordinatesThree a P)).yw =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo P).yw := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo]
    ring
  have eqzw : (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo (scaleCoordinatesThree a P)).zw =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo P).zw := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo, MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo]
    ring
  exact ⟨by rw [eqQ, hq, mul_zero], by rw [eqC, hc, mul_zero],
    by rw [eqxy, hxy, mul_zero],
    by rw [eqxz, hxz, mul_zero],
    by rw [eqxw, hxw, mul_zero],
    by rw [eqyz, hyz, mul_zero],
    by rw [eqyw, hyw, mul_zero],
    by rw [eqzw, hzw, mul_zero]⟩

private theorem nonsingular_two_of_nonzero {K : Type*} [Field K] [CharP K 2]
    (P : Coordinates4 K) (hP : P ≠ zeroCoordinatesThree) :
    ¬ MazurProof.RationalPointsN25QuotientSmoothF2.IsCanonicalSingular25CharTwo P := by
  classical
  intro hs
  obtain ⟨a, _, hnorm⟩ := normalizeCoordinatesThree_spec hP
  have hscaled := singular_two_scale a P hs
  rw [← hnorm] at hscaled
  have hcoords :
      MazurProof.RationalPointsN25QuotientSmoothF2.normalizedCoordinates25
        (normalizeCoordinatesThree P) =
      normalizedCoordinatesThree (normalizeCoordinatesThree P) := by
    cases normalizeCoordinatesThree P <;> rfl
  apply MazurProof.RationalPointsN25QuotientSmoothF2.normalized_projective_point_not_singular
    (normalizeCoordinatesThree P)
  rw [hcoords]
  exact hscaled

private theorem gradient_two_quadric {K : Type*} [Field K] [CharP K 2]
    (P : Coordinates4 K) (j : Fin 4) :
    canonicalQuadricGradient25 (coordinates4Vector25 P) j =
      coordinates4Vector25 (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo P) j := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg (a : K) : -a = a := CharTwo.neg_eq a
  fin_cases j <;> simp [canonicalQuadricGradient25, coordinates4Vector25,
    MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadricGradient25CharTwo, htwo, sub_eq_add_neg, hneg] <;> ring

private theorem gradient_two_cubic {K : Type*} [Field K] [CharP K 2]
    (P : Coordinates4 K) (j : Fin 4) :
    canonicalCubicGradient25 (coordinates4Vector25 P) j =
      coordinates4Vector25 (MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo P) j := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg (a : K) : -a = a := CharTwo.neg_eq a
  fin_cases j <;> simp [canonicalCubicGradient25, coordinates4Vector25,
    MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubicGradient25CharTwo, htwo, sub_eq_add_neg, hneg] <;> ring

private theorem singular_three_scale {K : Type*} [Field K]
    (a : K) (P : Coordinates4 K) (h : MazurProof.RationalPointsN25QuotientSmoothF3.IsCanonicalSingular25Three P) :
    MazurProof.RationalPointsN25QuotientSmoothF3.IsCanonicalSingular25Three (scaleCoordinatesThree a P) := by
  rcases h with ⟨hq, hc, hxy, hxz, hxw, hyz, hyw, hzw⟩
  have eqQ : MazurProof.RationalPointsN25QuotientKummerThree.canonicalQuadric25Three (scaleCoordinatesThree a P) =
      a^2 * MazurProof.RationalPointsN25QuotientKummerThree.canonicalQuadric25Three P := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientKummerThree.canonicalQuadric25Three]
    ring
  have eqC : MazurProof.RationalPointsN25QuotientKummerThree.canonicalCubic25Three (scaleCoordinatesThree a P) =
      a^3 * MazurProof.RationalPointsN25QuotientKummerThree.canonicalCubic25Three P := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientKummerThree.canonicalCubic25Three]
    ring
  have eqxy : (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three (scaleCoordinatesThree a P)).xy =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three P).xy := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three]
    ring
  have eqxz : (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three (scaleCoordinatesThree a P)).xz =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three P).xz := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three]
    ring
  have eqxw : (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three (scaleCoordinatesThree a P)).xw =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three P).xw := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three]
    ring
  have eqyz : (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three (scaleCoordinatesThree a P)).yz =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three P).yz := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three]
    ring
  have eqyw : (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three (scaleCoordinatesThree a P)).yw =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three P).yw := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three]
    ring
  have eqzw : (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three (scaleCoordinatesThree a P)).zw =
      a^3 * (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three P).zw := by
    dsimp [scaleCoordinatesThree, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three, MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three]
    ring
  exact ⟨by rw [eqQ, hq, mul_zero], by rw [eqC, hc, mul_zero],
    by rw [eqxy, hxy, mul_zero],
    by rw [eqxz, hxz, mul_zero],
    by rw [eqxw, hxw, mul_zero],
    by rw [eqyz, hyz, mul_zero],
    by rw [eqyw, hyw, mul_zero],
    by rw [eqzw, hzw, mul_zero]⟩

private theorem nonsingular_three_of_nonzero {K : Type*} [Field K] [CharP K 3]
    (P : Coordinates4 K) (hP : P ≠ zeroCoordinatesThree) :
    ¬ MazurProof.RationalPointsN25QuotientSmoothF3.IsCanonicalSingular25Three P := by
  classical
  intro hs
  obtain ⟨a, _, hnorm⟩ := normalizeCoordinatesThree_spec hP
  have hscaled := singular_three_scale a P hs
  rw [← hnorm] at hscaled
  exact MazurProof.RationalPointsN25QuotientSmoothF3.normalized_projective_point_not_singular _ hscaled

private theorem gradient_three_quadric {K : Type*} [Field K] [CharP K 3]
    (P : Coordinates4 K) (j : Fin 4) :
    canonicalQuadricGradient25 (coordinates4Vector25 P) j =
      coordinates4Vector25 (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three P) j := by
  have hthree : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have htwo : (2 : K) = -1 := by linear_combination hthree
  fin_cases j <;> simp [canonicalQuadricGradient25, coordinates4Vector25,
    MazurProof.RationalPointsN25QuotientSmoothF3.canonicalQuadricGradient25Three, htwo] <;> ring

private theorem gradient_three_cubic {K : Type*} [Field K] [CharP K 3]
    (P : Coordinates4 K) (j : Fin 4) :
    canonicalCubicGradient25 (coordinates4Vector25 P) j =
      coordinates4Vector25 (MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three P) j := by
  have hthree : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have htwo : (2 : K) = -1 := by linear_combination hthree
  fin_cases j <;> simp [canonicalCubicGradient25, coordinates4Vector25,
    MazurProof.RationalPointsN25QuotientSmoothF3.canonicalCubicGradient25Three, htwo] <;> ring

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

/-- On a canonical affine chart over either good characteristic, one minor
using only the three non-pivot columns is nonzero at every field-valued point. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] (i : Fin 4)
    (P : CanonicalChartPoint25 K i) :
    ∃ j k : Fin 4, j ≠ i ∧ k ≠ i ∧ j < k ∧
      MvPolynomial.eval P.coordinates (canonicalJacobianMinor25 K j k) ≠ 0 := by
  classical
  by_contra h
  have hminor (j k : Fin 4) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k) :
      canonicalQuadricGradient25 P.coordinates j * canonicalCubicGradient25 P.coordinates k -
        canonicalCubicGradient25 P.coordinates j * canonicalQuadricGradient25 P.coordinates k = 0 := by
    rw [← canonicalJacobianMinor25_eval]
    by_contra hm
    exact h ⟨j, k, hj, hk, hjk, hm⟩
  have hQ : (∑ j : Fin 4, P.coordinates j * canonicalQuadricGradient25 P.coordinates j) = 0 := by
    rw [canonicalQuadricGradient25_euler, P.quadric, mul_zero]
  have hC : (∑ j : Fin 4, P.coordinates j * canonicalCubicGradient25 P.coordinates j) = 0 := by
    rw [canonicalCubicGradient25_euler, P.cubic, mul_zero]
  have hzero := minors_zero_of_complementary_columns P.coordinates
    (canonicalQuadricGradient25 P.coordinates) (canonicalCubicGradient25 P.coordinates)
    i P.pivot hQ hC hminor
  let V : Coordinates4 K := ⟨P.coordinates 0, P.coordinates 1, P.coordinates 2, P.coordinates 3⟩
  have hcoords : coordinates4Vector25 V = P.coordinates := by
    funext j
    fin_cases j <;> rfl
  have hV : V ≠ zeroCoordinatesThree := by
    intro hv
    have hz : coordinates4Vector25 V i = 0 := by
      rw [hv]
      fin_cases i <;> rfl
    rw [hcoords, P.pivot] at hz
    exact one_ne_zero hz
  rw [← hcoords] at hzero
  rcases hp with rfl | rfl
  · apply nonsingular_two_of_nonzero V hV
    change MazurProof.RationalPointsN25QuotientSmoothF2.IsCanonicalSingular25CharTwo V
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have heq : MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo V =
          canonicalQuadric (P.coordinates 0) (P.coordinates 1)
            (P.coordinates 2) (P.coordinates 3) := by
        have hneg (a : K) : -a = a := CharTwo.neg_eq a
        dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalQuadric25CharTwo, V, canonicalQuadric]
        simp only [sub_eq_add_neg, hneg]
      exact heq.trans P.quadric
    · have heq : MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo V =
          canonicalCubic (P.coordinates 0) (P.coordinates 1)
            (P.coordinates 2) (P.coordinates 3) := by
        have hneg (a : K) : -a = a := CharTwo.neg_eq a
        dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalCubic25CharTwo, V, canonicalCubic]
        simp only [sub_eq_add_neg, hneg]
      exact heq.trans P.cubic
    · have hm := hzero 0 1
      rw [gradient_two_quadric, gradient_two_cubic,
        gradient_two_cubic, gradient_two_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo]
      linear_combination hm
    · have hm := hzero 0 2
      rw [gradient_two_quadric, gradient_two_cubic,
        gradient_two_cubic, gradient_two_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo]
      linear_combination hm
    · have hm := hzero 0 3
      rw [gradient_two_quadric, gradient_two_cubic,
        gradient_two_cubic, gradient_two_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo]
      linear_combination hm
    · have hm := hzero 1 2
      rw [gradient_two_quadric, gradient_two_cubic,
        gradient_two_cubic, gradient_two_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo]
      linear_combination hm
    · have hm := hzero 1 3
      rw [gradient_two_quadric, gradient_two_cubic,
        gradient_two_cubic, gradient_two_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo]
      linear_combination hm
    · have hm := hzero 2 3
      rw [gradient_two_quadric, gradient_two_cubic,
        gradient_two_cubic, gradient_two_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF2.canonicalJacobianMinors25CharTwo]
      linear_combination hm
  · apply nonsingular_three_of_nonzero V hV
    change MazurProof.RationalPointsN25QuotientSmoothF3.IsCanonicalSingular25Three V
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact P.quadric
    · exact P.cubic
    · have hm := hzero 0 1
      rw [gradient_three_quadric, gradient_three_cubic,
        gradient_three_cubic, gradient_three_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three]
      linear_combination hm
    · have hm := hzero 0 2
      rw [gradient_three_quadric, gradient_three_cubic,
        gradient_three_cubic, gradient_three_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three]
      linear_combination hm
    · have hm := hzero 0 3
      rw [gradient_three_quadric, gradient_three_cubic,
        gradient_three_cubic, gradient_three_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three]
      linear_combination hm
    · have hm := hzero 1 2
      rw [gradient_three_quadric, gradient_three_cubic,
        gradient_three_cubic, gradient_three_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three]
      linear_combination hm
    · have hm := hzero 1 3
      rw [gradient_three_quadric, gradient_three_cubic,
        gradient_three_cubic, gradient_three_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three]
      linear_combination hm
    · have hm := hzero 2 3
      rw [gradient_three_quadric, gradient_three_cubic,
        gradient_three_cubic, gradient_three_quadric] at hm
      dsimp [coordinates4Vector25] at hm
      dsimp [MazurProof.RationalPointsN25QuotientSmoothF3.canonicalJacobianMinors25Three]
      linear_combination hm

end N25

namespace N25

end N25
