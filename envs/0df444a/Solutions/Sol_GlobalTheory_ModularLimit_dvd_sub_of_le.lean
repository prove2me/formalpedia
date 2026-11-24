-- Prove2me | solution 1 for GlobalTheory.ModularLimit.dvd_sub_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:20.863342+00:00
-- url     : https://prove2.me/submissions/e8226f77-2c31-4ea8-8ba6-527ca16dadf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SmodEqIffDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ModularLimit
namespace GlobalTheory.ModularLimit
theorem _root_.solution {W : Type} [CommRing W] (x : W) (f : ℕ → W)
    (hf : ∀ k : ℕ, x ^ k ∣ f (k + 1) - f k) {m n : ℕ} (hmn : m ≤ n) :
    x ^ m ∣ f n - f m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hstep : x ^ m ∣ f (n + 1) - f n := (pow_dvd_pow x hmn).trans (hf n)
    have hsplit : f (n + 1) - f m = (f (n + 1) - f n) + (f n - f m) := by ring
    rw [hsplit]
    exact dvd_add hstep ih
end GlobalTheory.ModularLimit
