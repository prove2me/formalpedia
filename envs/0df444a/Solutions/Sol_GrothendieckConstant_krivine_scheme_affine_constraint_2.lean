-- Prove2me | solution 2 for GrothendieckConstant.krivine_scheme_affine_constraint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T14:32:21.940253+00:00
-- url     : https://prove2.me/submissions/abe758d5-541f-48b1-9aa2-5be188fc1fdb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckConstant_coeff_hermite_moments
import Theorems.Thm_GrothendieckLB_eq_35_36

open GrothendieckConstant GrothendieckLB

theorem solution (k : ℕ) (S : KrivineScheme k) :
    2 * coeffLinear S - 11 / 6 ≤ coeffCubic S := by
  obtain ⟨h₁, h₃⟩ := coeff_hermite_moments k S
  change coeffLinear S = (Real.pi / 2) * p1Inner S.f S.g at h₁
  change coeffCubic S = (Real.pi / 12) *
    ∑ i, ∑ j, ∑ l, cubicMoment S.f i j l * cubicMoment S.g i j l at h₃
  have hCubic : coeffCubic S = (Real.pi / 2) * p3Inner S.f S.g := by
    rw [h₃, p3Inner]
    ring

  have hHermite := (eq_35_36 (f := S.f) (g := S.g)
    ⟨S.measurable_f, S.f_sign⟩ ⟨S.measurable_g, S.g_sign⟩).2.2
  have h : 2 * coeffLinear S - coeffCubic S ≤ 11 / 6 := calc
    2 * coeffLinear S - coeffCubic S
        = (Real.pi / 2) * (2 * p1Inner S.f S.g - p3Inner S.f S.g) := by
          rw [h₁, hCubic]
          ring
    _ ≤ (Real.pi / 2) * (11 / 6 * ABPOnline.cG ^ 2) :=
          mul_le_mul_of_nonneg_left hHermite (by positivity)
    _ = 11 / 6 := by
          rw [ABPOnline.cG, Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi)]
          field_simp [Real.pi_ne_zero] <;> ring
  linarith only [h]
