-- Prove2me | solution 1 for MasulloGRH.isHLCS_ulift_lp_one
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:21:33.503194+00:00
-- url     : https://prove2.me/submissions/3ee11123-f793-4d4b-a9b6-66ff1c693bec

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH

universe u

/-- `ℓ¹` (lifted to universe `u`) is a Hausdorff locally convex space: its norm topology is
polynormable, hence given by the family of all its continuous seminorms, and it is metric. -/
theorem solution : IsHLCS (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) := by
  have hP : PolynormableSpace ℂ (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) :=
    (norm_withSeminorms ℂ (ULift.{u} (lp (fun _ : ℕ => ℂ) 1))).toPolynormableSpace
  exact ⟨⟨{p : Seminorm ℂ (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) // Continuous p},
    ⟨⟨0, continuous_const⟩⟩, fun p => p.1, PolynormableSpace.withSeminorms ℂ _⟩, inferInstance⟩
