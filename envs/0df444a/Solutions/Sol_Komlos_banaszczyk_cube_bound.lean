-- Prove2me | solution 1 for Komlos.banaszczyk_cube_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:35:06.167714+00:00
-- url     : https://prove2.me/submissions/64d328c4-d165-45ae-b52f-72ab74394759
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Komlos_gaussian_cube_half_measure
import Theorems.Thm_Komlos_banaszczyk_convex_body

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace BanaszczykGaussianCube

lemma cube_compact (m : ℕ) (r : ℝ) :
    IsCompact {x : EuclideanSpace ℝ (Fin m) | ∀ j, |x j| ≤ r} := by
  have hc : IsCompact (Icc (fun _ : Fin m => -r) (fun _ => r)) := isCompact_Icc
  have he : {x : EuclideanSpace ℝ (Fin m) | ∀ j, |x j| ≤ r} =
      (WithLp.toLp 2) '' Icc (fun _ : Fin m => -r) (fun _ => r) := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ?_, by simp⟩
      constructor <;> intro j
      · exact (abs_le.mp (hx j)).1
      · exact (abs_le.mp (hx j)).2
    · rintro ⟨y,hy,rfl⟩ j
      exact abs_le.mpr ⟨hy.1 j,hy.2 j⟩
  rw [he]
  exact hc.image (by fun_prop)

lemma cube_convex (m : ℕ) (r : ℝ) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin m) | ∀ j, |x j| ≤ r} := by
  intro x hx y hy a b ha hb hab j
  change |a*x j+b*y j| ≤ r
  calc
    _ ≤ |a*x j|+|b*y j| := abs_add_le _ _
    _ = a*|x j|+b*|y j| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a*r+b*r := add_le_add (mul_le_mul_of_nonneg_left (hx j) ha)
      (mul_le_mul_of_nonneg_left (hy j) hb)
    _ = r := by rw [← add_mul, hab, one_mul]

end BanaszczykGaussianCube

open Komlos BanaszczykGaussianCube

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (m + 2)) := by
  refine ⟨10, by norm_num, ?_⟩
  intro n m v hv
  let w : Fin n → EuclideanSpace ℝ (Fin m) := fun i => (1/5:ℝ) • v i
  have hw : ∀ i, ‖w i‖ ≤ (1/5 : ℝ) := by
    intro i
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    nlinarith [hv i]
  let r := 2 * Real.sqrt (Real.log ((m:ℝ)+2))
  let K : Set (EuclideanSpace ℝ (Fin m)) := {x | ∀ j, |x j| ≤ r}
  obtain ⟨eps,heps,hsum⟩ := banaszczyk_convex_body n m w hw K (cube_convex m r) (cube_compact m r)
    (gaussian_cube_half_measure m)
  refine ⟨eps,heps,?_⟩
  intro j
  have hj := hsum j
  have heq : (∑ i, eps i • w i) j = (1/5:ℝ) * ∑ i, eps i * v i j := by
    simp [w]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, abs_mul] at hj
  norm_num at hj
  dsimp [r] at hj
  nlinarith

