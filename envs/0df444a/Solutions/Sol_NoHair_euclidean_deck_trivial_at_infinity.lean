-- Prove2me | solution 1 for NoHair.euclidean_deck_trivial_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:50:48.203104+00:00
-- url     : https://prove2.me/submissions/52d71366-edf8-4aba-bd86-0a7c1720a3e3

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution {Q : Type*} (p : ADMPoint → Q) (R : ℝ) (sheet : Set.InjOn p {x | R < ‖x‖})
    (d : ADMPoint ≃ᵢ ADMPoint) (deck : ∀ z, p (d z)=p z) : ∀ x : ADMPoint, d x=x := by
  let R' := max R 0 + ‖d 0‖
  have fixes (z : ADMPoint) (large : R' < ‖z‖) : d z = z := by
    have triangle := dist_triangle (d z) (0:ADMPoint) (d 0)
    rw [d.dist_eq,dist_zero_right,dist_zero_right,dist_zero_left] at triangle
    apply sheet _ _ (deck z)
    · change R < ‖d z‖
      dsimp only [R'] at large
      linarith only [large,triangle,le_max_left R 0]
    · change R < ‖z‖
      dsimp only [R'] at large
      linarith only [large,le_max_left R 0,norm_nonneg (d 0)]
  intro x
  let t := R' + ‖x‖ + 1
  have tp : 0 ≤ t := by
    dsimp only [t,R']
    linarith only [le_max_right R 0,norm_nonneg (d 0),norm_nonneg x]
  let v : ADMPoint := EuclideanSpace.single 0 t
  have len : ‖v‖=t := by simp only [v,EuclideanSpace.norm_single,Real.norm_eq_abs,abs_of_nonneg tp]
  have h1 := norm_sub_le (x+v) x
  have h2 := norm_sub_le x (x-v)
  rw [show (x+v)-x=v by abel,len] at h1
  rw [show x-(x-v)=v by abel,len] at h2
  have a : d (x+v)=x+v := fixes _ (by dsimp only [t] at h1; linarith only [h1])
  have b : d (x-v)=x-v := fixes _ (by dsimp only [t] at h2; linarith only [h2])
  have middle : midpoint ℝ (x+v) (x-v) = x := by
    rw [midpoint_eq_smul_add,show (x+v)+(x-v)=(2:ℝ) • x by rw [two_smul]; abel,
      smul_smul,invOf_mul_self,one_smul]
  simpa only [middle] using d.midpoint_fixed a b
