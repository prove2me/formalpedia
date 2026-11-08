-- Prove2me | solution 1 for JointNonManip.sne_extreme_points
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:08:27.280242+00:00
-- url     : https://prove2.me/submissions/652fafc7-e568-47d9-a692-ffe0629cf9bc

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

open JointNonManip in
theorem solution {A0 : Type} [Fintype A0] [DecidableEq A0]
    {L : Type} [Fintype L] [DecidableEq L]
    {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1) :
    ∀ s ∈ Set.extremePoints ℝ (SNE u), ∃ (y : A0 → ℝ) (x : (i : L) → Act i → ℝ),
      AGT.IsLottery y ∧ AGT.IsMixedNash (inducedUtility u y) x ∧
        s = otimes y (AGT.profileProb x) := by
  intro s hs
  unfold SNE at hs
  have h : s ∈ ENE u := extremePoints_convexHull_subset hs
  exact h
