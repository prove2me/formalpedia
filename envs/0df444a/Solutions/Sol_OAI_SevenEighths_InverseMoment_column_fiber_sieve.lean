-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.column_fiber_sieve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:49.200756+00:00
-- url     : https://prove2.me/submissions/c84852df-051a-48f5-822a-2a593215125c

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition
import Theorems.Thm_OAI_SevenEighths_InverseMoment_finite_expansion_energy


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {K X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (φ : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ) (hQ : 0 ≤ Q)
    (hφ : ∀ x ∈ source, φ x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter (fun x => φ x = y)).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y * f y‖ ^ 2) ≤
        Q * ∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (φ x) * a x‖ ^ 2) ≤
      Q * D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
  let f : Y → ℂ := fun y => ∑ x ∈ source with φ x = y, a x
  have he (k : K) : (∑ x ∈ source, q k (φ x) * a x) =
      ∑ y ∈ target, q k y * f y := by
    rw [← Finset.sum_fiberwise_of_maps_to hφ]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hf := finite_expansion_energy target source
    (fun y => source.filter (fun x => φ x = y)) (fun _ _ => 1) (fun _ => a) D
    (fun _ _ => Finset.filter_subset _ _) (by simp) hfiber
  have hf' : (∑ y ∈ target, ‖f y‖ ^ 2) ≤ D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
    have hrhs : (∑ x ∈ source, ∑ y ∈ target,
        if x ∈ source.filter (fun x => φ x = y) then ‖a x‖ ^ 2 else 0) =
        ∑ x ∈ source, ‖a x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx, hφ x hx]
    rw [hrhs] at hf
    simpa only [one_mul, f] using hf
  simp_rw [he]
  exact (hsieve f).trans (by
    calc
      _ ≤ Q * (D * ∑ x ∈ source, ‖a x‖ ^ 2) := mul_le_mul_of_nonneg_left hf' hQ
      _ = _ := by ring)
end OAI.SevenEighths.InverseMoment
