-- Prove2me | solution 1 for GlobalTheory.PMonE.window_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:39.931725+00:00
-- url     : https://prove2.me/submissions/658a0f5b-16b4-4cae-8c1a-08d634bd759c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAdditive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE
namespace GlobalTheory.PMonE
theorem _root_.solution (q : ℝ) (hq : 2 ≤ q) (r : ℤ) (α f : ℤ → ℝ) (hα : Antitone α)
    (hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * (q ^ (r - J) - 1)) :
    (∀ J, J ≤ r → f J + α J ≤ f r + α r) ∧
    (∀ J, r + 1 ≤ J → f J - α J / 2 ≤ f r - α (r + 1) / 2) := by
  have hd : ∀ J, 0 ≤ α J - α (J + 1) := fun J => sub_nonneg.2 (hα (by omega))
  have hq1 : (1 : ℝ) ≤ q := by linarith
  constructor
  · intro J hJ
    induction J, hJ using Int.leInductionDown with
    | base => exact le_rfl
    | pred n hn ih =>
      have h1 := hf (n - 1)
      have h2 := hd (n - 1)
      rw [sub_add_cancel] at h1 h2
      have h3 : q ^ (1 : ℤ) ≤ q ^ (r - (n - 1)) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_one] at h3
      nlinarith [mul_nonneg h2 (show 0 ≤ q ^ (r - (n - 1)) - 2 by linarith)]
  · intro J hJ
    induction J, hJ using Int.leInduction with
    | base =>
      have h1 := hf r
      rw [sub_self, zpow_zero, sub_self, mul_zero] at h1
      linarith
    | succ n hn ih =>
      have h1 := hf n
      have h2 := hd n
      have h3 : q ^ (r - n) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_neg_one] at h3
      have h4 : q⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
      nlinarith [mul_nonneg h2 (show 0 ≤ 2⁻¹ - q ^ (r - n) by linarith)]
end GlobalTheory.PMonE
