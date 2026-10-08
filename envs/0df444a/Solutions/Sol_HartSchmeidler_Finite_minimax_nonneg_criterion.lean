-- Prove2me | solution 1 for HartSchmeidler.Finite.minimax_nonneg_criterion
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:35:06.617915+00:00
-- url     : https://prove2.me/submissions/1dfbe0a6-aabb-4df4-88f5-7ab3ec2de991

import Mathlib
import Definitions.Def_agt_games

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HsWork

open Finset

theorem isLottery_iff_mem {X : Type*} [Fintype X] (x : X → ℝ) :
    AGT.IsLottery x ↔ x ∈ stdSimplex ℝ X := Iff.rfl

theorem minimax_nonneg_criterion {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : X → Y → ℝ)
    (hA : ∀ y : Y → ℝ, AGT.IsLottery y →
      ∃ x : X → ℝ, AGT.IsLottery x ∧
        0 ≤ ∑ a, ∑ b, x a * y b * A a b) :
    ∃ x : X → ℝ, AGT.IsLottery x ∧
      ∀ y : Y → ℝ, AGT.IsLottery y →
        0 ≤ ∑ a, ∑ b, x a * y b * A a b := by
  classical
  let f : (Y → ℝ) → (X → ℝ) → ℝ := fun y x => ∑ a, ∑ b, x a * y b * A a b
  have hf_cont_y : ∀ x : X → ℝ, Continuous fun y : Y → ℝ => f y x := by
    intro x; simp only [f]; fun_prop
  have hf_cont_x : ∀ y : Y → ℝ, Continuous fun x : X → ℝ => f y x := by
    intro y; simp only [f]; fun_prop
  have hf_lin_y : ∀ (x : X → ℝ) (y y' : Y → ℝ) (a b : ℝ),
      f (a • y + b • y') x = a * f y x + b * f y' x := by
    intro x y y' a b
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  have hf_lin_x : ∀ (y : Y → ℝ) (x x' : X → ℝ) (a b : ℝ),
      f y (a • x + b • x') = a * f y x + b * f y x' := by
    intro y x x' a b
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  have neY : (stdSimplex ℝ Y).Nonempty := by
    obtain ⟨y0⟩ := ‹Nonempty Y›
    exact ⟨Pi.single y0 1, by simp [stdSimplex, Pi.single_apply]; intro i; split_ifs <;> norm_num⟩
  have neX : (stdSimplex ℝ X).Nonempty := by
    obtain ⟨x0⟩ := ‹Nonempty X›
    exact ⟨Pi.single x0 1, by simp [stdSimplex, Pi.single_apply]; intro i; split_ifs <;> norm_num⟩
  have hconvY : ∀ x : X → ℝ, ConvexOn ℝ (stdSimplex ℝ Y) (fun y => f y x) := fun x =>
    ⟨convex_stdSimplex ℝ Y, fun y _ y' _ a b ha hb hab => by
      show f (a • y + b • y') x ≤ a • f y x + b • f y' x
      rw [hf_lin_y]; simp [smul_eq_mul]⟩
  have hconcX : ∀ y : Y → ℝ, ConcaveOn ℝ (stdSimplex ℝ X) (fun x => f y x) := fun y =>
    ⟨convex_stdSimplex ℝ X, fun x _ x' _ a b ha hb hab => by
      show a • f y x + b • f y x' ≤ f y (a • x + b • x')
      rw [hf_lin_x]; simp [smul_eq_mul]⟩
  obtain ⟨ys, hys, xs, hxs, hsad⟩ := Sion.exists_isSaddlePointOn (X := stdSimplex ℝ Y)
    (Y := stdSimplex ℝ X) (f := f) neY (convex_stdSimplex ℝ Y) (isCompact_stdSimplex ℝ Y)
    (fun x _ => (hf_cont_y x).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun x _ => (hconvY x).quasiconvexOn)
    (convex_stdSimplex ℝ X) neX (isCompact_stdSimplex ℝ X)
    (fun y _ => (hf_cont_x y).upperSemicontinuous.upperSemicontinuousOn _)
    (fun y _ => (hconcX y).quasiconcaveOn)
  obtain ⟨xA, hxA, hxA0⟩ := hA ys hys
  exact ⟨xs, hxs, fun y hy => le_trans hxA0 (hsad y hy xA hxA)⟩

end HsWork

open Finset

theorem solution {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (A : X → Y → ℝ)
    (hA : ∀ y : Y → ℝ, AGT.IsLottery y →
      ∃ x : X → ℝ, AGT.IsLottery x ∧
        0 ≤ ∑ a, ∑ b, x a * y b * A a b) :
    ∃ x : X → ℝ, AGT.IsLottery x ∧
      ∀ y : Y → ℝ, AGT.IsLottery y →
        0 ≤ ∑ a, ∑ b, x a * y b * A a b :=
  HsWork.minimax_nonneg_criterion A hA

#print axioms solution
