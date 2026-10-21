-- Prove2me | solution 1 for HessianDamping.IGAHDSC.vK_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:38:42.064369+00:00
-- url     : https://prove2.me/submissions/5e9346a4-3b73-46dc-8d91-8777f81ec89d

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

set_option autoImplicit false

open HessianDamping.IGAHDSC

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (μ β s : ℝ) (hμ : 0 < μ) (hs : 0 < s)
    (xstar : H) (x : ℕ → H) (hrun : IsIGAHDSCRun f μ β s x)
    (k : ℕ) (hk : 1 ≤ k) :
    vK f μ β s x xstar (k + 1) - vK f μ β s x xstar k =
      -(Real.sqrt μ) • (x (k + 1) - x k) -
        Real.sqrt s • gradient f (x k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := hrun (j + 1) hk
  dsimp only at h
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ μ = a ^ 2 := ⟨Real.sqrt μ, Real.sqrt_pos.2 hμ, (Real.sq_sqrt hμ.le).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ s = b ^ 2 := ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
  have hr : Real.sqrt (a ^ 2 * b ^ 2) = a * b := by
    rw [← mul_pow]; exact Real.sqrt_sq (by positivity)
  unfold vK
  simp only [Nat.add_sub_cancel, hr, Real.sqrt_sq ha.le, Real.sqrt_sq hb.le] at h ⊢
  rw [h]
  have hab : (1 + a * b) ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring
