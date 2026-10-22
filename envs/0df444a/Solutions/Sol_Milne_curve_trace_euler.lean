-- Prove2me | solution 1 for Milne.curve_trace_euler
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:11:31.450573+00:00
-- url     : https://prove2.me/submissions/e5c88358-e282-4de3-a0a3-7b4a310fa44a

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta
universe u v

open Milne

theorem solution (W : CorrWorld.{u, v}) (g : ℕ) :
    W.trId (W.curve g) (W.delta (W.curve g)) = (2 : ℚ) - 2 * (g : ℚ) := by
  -- (a + b) + (-b) = a in the correspondence group
  have cancel : ∀ (a b : W.Corr (W.curve g) (W.curve g)),
      W.add (W.add a b) (W.neg b) = a := by
    intro a b
    rw [W.add_assoc, W.add_neg_cancel, W.add_zero]
  -- first split: Δ = (π₀ + π₁) + π₂
  have h1 := W.trAdd (W.delta (W.curve g)) (W.pi2 g) (W.cc_id_left _) (W.pi2_idem g)
    (by rw [W.cc_id_left, W.cc_id_right])
  have hd : W.add (W.delta (W.curve g)) (W.neg (W.pi2 g)) = W.add (W.pi0 g) (W.pi1 g) := by
    rw [← W.curve_diag g, cancel]
  rw [hd] at h1
  -- second split: π₀ + π₁ = π₀ + π₁
  have hidem : W.cc (W.add (W.pi0 g) (W.pi1 g)) (W.add (W.pi0 g) (W.pi1 g)) =
      W.add (W.pi0 g) (W.pi1 g) := by
    rw [W.cc_add_left, W.cc_add_right, W.cc_add_right, W.pi0_idem, W.pi1_idem,
      W.pi01_zero, W.pi10_zero, W.add_zero, W.zero_add]
  have hsand : W.cc (W.cc (W.add (W.pi0 g) (W.pi1 g)) (W.pi1 g)) (W.add (W.pi0 g) (W.pi1 g)) =
      W.pi1 g := by
    rw [W.cc_add_left, W.pi01_zero, W.pi1_idem, W.zero_add, W.cc_add_right, W.pi10_zero,
      W.pi1_idem, W.zero_add]
  have h2 := W.trAdd (W.add (W.pi0 g) (W.pi1 g)) (W.pi1 g) hidem (W.pi1_idem g) hsand
  rw [cancel] at h2
  rw [h1, h2, W.tr_pi0, W.tr_pi1, W.tr_pi2]
  ring
