-- Prove2me | solution 1 for GlobalTheory.JR.quadratic_star_structure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:54.531968+00:00
-- url     : https://prove2.me/submissions/7eca20b7-a992-4afb-a069-a17d55b74f40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (d : K) (hb0 : b 0 = 1) (hs : star (b 1) = - b 1)
    (hd : b 1 * b 1 = algebraMap K L d) (hK : ∀ x : K, star (algebraMap K L x) = algebraMap K L x)
    (hdu : IsUnit d) (h2 : IsUnit (2 : K)) :
    Function.Injective (algebraMap K L) ∧ (∀ y : L, algebraMap K L (Algebra.norm K y) = y * star y) ∧
      (∀ y : L, algebraMap K L (Algebra.trace K L y) = y + star y) ∧
      (∀ y' : L, (∀ y : L, Algebra.trace K L (star y' * y) = 0) → y' = 0) := by
  have hrep0 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 0 = a := by
    intro a c; simp
  have hrep1 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 1 = c := by
    intro a c; simp
  have hexp : ∀ y : L, y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [Fin.sum_univ_two]
  have hsmul : ∀ (c : K) (z : L), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, hK, mul_comm]
  have hstar : ∀ y : L, star y = b.repr y 0 • b 0 + (-b.repr y 1) • b 1 := by
    intro y
    conv_lhs => rw [hexp y]
    rw [star_add, hsmul, hsmul, hb0, star_one, hs, smul_neg, neg_smul]
  have hmul : ∀ z : L, z * b 1 = (b.repr z 1 * d) • b 0 + b.repr z 0 • b 1 := by
    intro z
    conv_lhs => rw [hexp z]
    simp only [Algebra.smul_def, hb0, mul_one, map_mul, add_mul]
    linear_combination (algebraMap K L (b.repr z 1)) * hd
  have hc0 : ∀ z : L, b.repr (z * b 0) = b.repr z := by
    intro z; rw [hb0, mul_one]
  have htr : ∀ z : L, Algebra.trace K L z = b.repr z 0 + b.repr z 0 := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep1]
  have hmap : ∀ x : K, algebraMap K L x = x • b 0 := by
    intro x; rw [hb0, Algebra.algebraMap_eq_smul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hmap] at hx
    have := hrep0 x 0
    rw [zero_smul, add_zero, hx] at this
    simp at this
    exact this.symm
  · intro y
    rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep0, hrep1]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) * (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [Algebra.smul_def, hb0, mul_one, map_mul, map_sub, map_neg]
          linear_combination (algebraMap K L (b.repr y 1) * algebraMap K L (b.repr y 1)) * hd
      _ = y * star y := by rw [← hexp y, ← hstar y]
  · intro y
    rw [htr, hmap]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) + (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [add_smul, neg_smul]; abel
      _ = y + star y := by rw [← hexp y, ← hstar y]
  · intro y' hy'
    have g1 := hy' 1
    have g2 := hy' (b 1)
    rw [mul_one, htr, hstar, hrep0] at g1
    rw [hmul, htr, hrep0, hstar, hrep1] at g2
    have hp : b.repr y' 0 = 0 := by
      have h3 : (2 : K) * b.repr y' 0 = 0 := by rw [two_mul]; exact g1
      exact h2.mul_right_eq_zero.mp h3
    have hq : b.repr y' 1 = 0 := by
      have h3 : (2 : K) * (b.repr y' 1 * d) = 0 := by linear_combination -g2
      exact hdu.mul_left_eq_zero.mp (h2.mul_right_eq_zero.mp h3)
    rw [hexp y', hp, hq, zero_smul, zero_smul, add_zero]
end GlobalTheory.JR
