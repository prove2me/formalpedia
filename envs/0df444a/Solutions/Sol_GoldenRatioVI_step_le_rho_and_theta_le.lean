-- Prove2me | solution 1 for GoldenRatioVI.step_le_rho_and_theta_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:26:42.375827+00:00
-- url     : https://prove2.me/submissions/bd741c76-d354-4d5f-9a47-8bdf96f91911

import Mathlib
import Definitions.Def_GoldenRatioVI_IsEGRAALRun

open GoldenRatioVI in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {D : Set E} {g : E → ℝ} {F : E → E} {phi lam0 lbar : ℝ}
    {z zbar : ℕ → E} {lam theta : ℕ → ℝ}
    (hphi : 1 < phi) (hphiG : phi ≤ Real.goldenRatio) (hlam0 : 0 < lam0) (hlbar : 0 < lbar)
    (hrun : IsEGRAALRun D g F phi lam0 lbar z zbar lam theta) (k : ℕ) (hk : 1 ≤ k) :
    lam k ≤ lam (k - 1) * (1 / phi + 1 / phi ^ 2) ∧ theta k - 1 - 1 / phi ≤ 0 := by
  obtain ⟨-, hl0, ht0, hstep⟩ := hrun
  have hphi0 : 0 < phi := by linarith
  have hc : 0 < 1 / phi + 1 / phi ^ 2 := by positivity
  have hle : ∀ j, 1 ≤ j → lam j ≤ (1 / phi + 1 / phi ^ 2) * lam (j - 1) := by
    intro j hj
    rw [(hstep j hj).1]
    unfold egraalStep
    split_ifs
    · exact min_le_left _ _
    · exact (min_le_left _ _).trans (min_le_left _ _)
  have hpos : ∀ j, 0 < lam j ∧ 0 < theta j := by
    intro j
    induction j with
    | zero => rw [hl0, ht0]; exact ⟨hlam0, one_pos⟩
    | succ j ih =>
      obtain ⟨hlj, htj⟩ := ih
      have hs := hstep (j + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hs
      have hl : 0 < lam (j + 1) := by
        rw [hs.1]
        unfold egraalStep
        split_ifs with hF
        · exact lt_min (by positivity) hlbar
        · have hz : z (j + 1) ≠ z j := fun h => hF (by rw [h])
          have h1 : 0 < ‖z (j + 1) - z j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
          have h2 : 0 < ‖F (z (j + 1)) - F (z j)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hF)
          exact lt_min (lt_min (by positivity) (by positivity)) hlbar
      refine ⟨hl, ?_⟩
      rw [hs.2.2.2]
      positivity
  have hprev := (hpos (k - 1)).1
  refine ⟨by rw [mul_comm]; exact hle k hk, ?_⟩
  rw [(hstep k hk).2.2.2]
  have h1 : lam k / lam (k - 1) ≤ 1 / phi + 1 / phi ^ 2 := by
    rw [div_le_iff₀ hprev]; exact hle k hk
  have h2 : lam k / lam (k - 1) * phi ≤ (1 / phi + 1 / phi ^ 2) * phi :=
    mul_le_mul_of_nonneg_right h1 hphi0.le
  have h3 : (1 / phi + 1 / phi ^ 2) * phi = 1 + 1 / phi := by field_simp
  linarith
