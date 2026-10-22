-- Prove2me | solution 1 for HessianDamping.IGAHD.vK_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:33:44.336424+00:00
-- url     : https://prove2.me/submissions/b491f020-ea51-45db-8257-b74c40edf24c

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting
set_option autoImplicit false
open HessianDamping.IGAHD

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y)
    (k : ℕ) (hk : 1 ≤ k) :
    vK f α β s x xstar (k + 1) - vK f α β s x xstar k =
      -(s * tK α (k + 1)) • gradient f (y k) := by
  obtain ⟨hy, hx1⟩ := hrun k hk
  have hα1 : α - 1 ≠ 0 := by intro h; linarith
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have c1 : 1 + tK α (k + 1) * (1 - α / (k : ℝ)) - tK α k = 0 := by
    unfold tK; push_cast; field_simp; ring
  have c2 : tK α (k + 1) - tK α (k + 1) / (k : ℝ) - tK α k = 0 := by
    unfold tK; push_cast; field_simp; ring
  unfold vK
  simp only [Nat.add_sub_cancel]
  have hx2 : x (k + 1) = x k + (1 - α / (k : ℝ)) • (x k - x (k - 1))
          - (β * Real.sqrt s) • (gradient f (x k) - gradient f (x (k - 1)))
          - (β * Real.sqrt s / (k : ℝ)) • gradient f (x (k - 1))
          - s • gradient f (y k) := by
    rw [hx1, hy]
  rw [hx2]
  have key : ((x k - xstar) + tK α (k + 1) •
        ((x k + (1 - α / (k : ℝ)) • (x k - x (k - 1))
          - (β * Real.sqrt s) • (gradient f (x k) - gradient f (x (k - 1)))
          - (β * Real.sqrt s / (k : ℝ)) • gradient f (x (k - 1))
          - s • gradient f (y k)) - x k + (β * Real.sqrt s) • gradient f (x k))) -
      ((x (k - 1) - xstar) + tK α k •
        (x k - x (k - 1) + (β * Real.sqrt s) • gradient f (x (k - 1)))) +
      (s * tK α (k + 1)) • gradient f (y k) =
      (1 + tK α (k + 1) * (1 - α / (k : ℝ)) - tK α k) • (x k - x (k - 1)) +
      (β * Real.sqrt s * (tK α (k + 1) - tK α (k + 1) / (k : ℝ) - tK α k)) •
        gradient f (x (k - 1)) := by
    module
  rw [c1, c2, zero_smul, mul_zero, zero_smul, add_zero] at key
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left key
