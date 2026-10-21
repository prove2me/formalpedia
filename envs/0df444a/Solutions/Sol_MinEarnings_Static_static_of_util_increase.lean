-- Prove2me | solution 1 for MinEarnings.Static.static_of_util_increase
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:08:53.797149+00:00
-- url     : https://prove2.me/submissions/ee0f0471-e9e5-4136-8712-20f98b5c9161

import Mathlib
import Definitions.Def_MinEarnings_Static_Setting

set_option autoImplicit false
open MinEarnings.Threshold MinEarnings.Static

lemma mea_util_pos (D S : ℝ → ℝ) (hP : Primitives D S) {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    0 < util D S p z := by
  unfold util quantity
  exact div_pos (lt_min (hP.D_pos p hp) (hP.S_pos z hz)) (hP.S_pos z hz)

lemma mea_util_le_one (D S : ℝ → ℝ) (hP : Primitives D S) {p z : ℝ} (hz : 0 < z) :
    util D S p z ≤ 1 := by
  unfold util quantity
  rw [div_le_one (hP.S_pos z hz)]
  exact min_le_right _ _

lemma mea_static_of_floor (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S)
    (w z : ℕ → ℝ) (hfeas : IsFeasible w w) (heq : IsEquilibrium D S w w z) (t : ℕ)
    (hwt : M / util D S (w t) (z t) ≤ w t) : IsStaticallyStable D S M :=
  ⟨w t, w t, z t, util D S (w t) (z t), (hfeas t).2, (hfeas t).2, (heq t).1.le,
    mea_util_pos D S hP (hfeas t).2 (heq t).1, mea_util_le_one D S hP (heq t).1, rfl, (heq t).2,
    hwt, le_rfl⟩

lemma mea_static_of_inc (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : IsFeasible w w) (heq : IsEquilibrium D S w w z)
    (hrule : MinEarningsRule D S M w w z) (t : ℕ)
    (hinc : util D S (w t) (z t) ≤ util D S (w (t + 1)) (z (t + 1))) :
    IsStaticallyStable D S M := by
  refine mea_static_of_floor D S M hP w z hfeas heq (t + 1) ?_
  calc M / util D S (w (t + 1)) (z (t + 1)) ≤ M / util D S (w t) (z t) :=
        div_le_div_of_nonneg_left hM.le (mea_util_pos D S hP (hfeas t).2 (heq t).1) hinc
    _ ≤ w (t + 1) := hrule t

lemma mea_static_implies_stable (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S) (hM : 0 < M) :
    IsStaticallyStable D S M → IsStable D S M := by
  rintro ⟨p, w, z, u, hp, hw, hz, hu0, hu1, hu, hzw, hMu, hwp⟩
  have hwpos : 0 < w := lt_of_lt_of_le (div_pos hM hu0) hMu
  have hzpos : 0 < z := by rw [hzw]; exact mul_pos hwpos hu0
  refine ⟨fun _ => p, fun _ => w, fun _ => z, ?_, ?_, ?_, ⟨w, fun _ => le_rfl⟩, ?_⟩
  · exact fun _ => ⟨hp, hw⟩
  · exact fun _ => ⟨hzpos, by rw [← hu]; exact hzw⟩
  · intro t; show M / util D S p z ≤ w; rw [← hu]; exact hMu
  · refine Filter.Eventually.of_forall (fun t => ?_)
    show 0 ≤ (p - w) * quantity D S p z
    exact mul_nonneg (sub_nonneg.2 hwp) (le_min (hP.D_pos p hp).le (hP.S_pos z hzpos).le)

theorem solution (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : MinEarnings.Threshold.IsFeasible w w) (heq : MinEarnings.Threshold.IsEquilibrium D S w w z)
    (hrule : MinEarnings.Threshold.MinEarningsRule D S M w w z) (t : ℕ)
    (hinc : MinEarnings.Threshold.util D S (w t) (z t) ≤ MinEarnings.Threshold.util D S (w (t + 1)) (z (t + 1))) :
    IsStaticallyStable D S M :=
  mea_static_of_inc D S M hP hM w z hfeas heq hrule t hinc
