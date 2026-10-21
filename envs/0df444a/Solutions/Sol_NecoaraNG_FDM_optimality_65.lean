-- Prove2me | solution 1 for NecoaraNG.FDM.optimality_65
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:46:38.52448+00:00
-- url     : https://prove2.me/submissions/bba48725-5cbb-4b70-8b9d-80d0567ae7e4

import Mathlib
import Definitions.Def_NecoaraNG_FDM_Setting

set_option autoImplicit false

section NGHSec
open scoped InnerProductSpace
open NecoaraNG.Chain Filter Topology

namespace NGH
variable {n : ℕ}

theorem line_mem {X : Set (E n)} (hX : Convex ℝ X) {x y : E n} (hx : x ∈ X) (hy : y ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ X := by
  have := hX hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  convert this using 1
  module


theorem proj_ineq {X : Set (E n)} (hX : Convex ℝ X) {u p : E n} (hp : IsNearest X u p)
    {z : E n} (hz : z ∈ X) : ⟪u - p, z - p⟫_ℝ ≤ 0 := by
  by_contra hcon
  push Not at hcon
  set a := ⟪u - p, z - p⟫_ℝ with ha
  set b := ‖z - p‖ ^ 2 with hb
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 2 * a ≤ t * b := by
    intro t ht0 ht1
    have hq := line_mem hX hp.1 hz ⟨ht0.le, ht1⟩
    have h1 := hp.2 _ hq
    have h2 : ‖u - p‖ ^ 2 ≤ ‖u - (p + t • (z - p))‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e : u - (p + t • (z - p)) = (u - p) - t • (z - p) := by module
    rw [e] at h2
    have h3 := norm_sub_sq_real (u - p) (t • (z - p))
    have h4 : ‖t • (z - p)‖ ^ 2 = t ^ 2 * b := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [real_inner_smul_right] at h3
    have : t * (t * b - 2 * a) ≥ 0 := by nlinarith
    have := (mul_nonneg_iff_of_pos_left ht0).1 this
    linarith
  have hb0 : 0 < b := by
    have := key 1 one_pos le_rfl
    linarith
  have h1 := key (min 1 (a / b)) (lt_min one_pos (div_pos hcon hb0)) (min_le_left _ _)
  have h2 : min 1 (a / b) * b ≤ a / b * b :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hb0.le
  rw [div_mul_cancel₀ _ hb0.ne'] at h2
  linarith


end NGH
end NGHSec

open NecoaraNG.FDM
open scoped InnerProductSpace

theorem solution {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (hXconv : Convex ℝ X) (f : NecoaraNG.Chain.E n → ℝ)
    (β L Lbar : ℝ) (α : ℕ → ℝ) (e x : ℕ → NecoaraNG.Chain.E n) (hrun : IsFDMRun X f β L Lbar α e x) :
    ∀ k : ℕ, ∀ z ∈ X,
      0 ≤ ⟪x (k + 1) - x k + α k • gradient f (x k) - e k, z - x (k + 1)⟫_ℝ := by
  intro k z hz
  have h := NGH.proj_ineq hXconv (hrun.2 k).1 hz
  have e1 : x (k + 1) - x k + α k • gradient f (x k) - e k
      = -(x k - α k • gradient f (x k) + e k - x (k + 1)) := by module
  rw [e1, inner_neg_left]
  linarith
