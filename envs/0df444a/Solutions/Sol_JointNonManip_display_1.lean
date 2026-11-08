-- Prove2me | solution 1 for JointNonManip.display_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:39:59.589026+00:00
-- url     : https://prove2.me/submissions/fb7bb010-bdb8-4fb4-a7b7-0a7b3bbd90c6

import Mathlib
import Definitions.Def_JointNonManip_Algorithm1

open JointNonManip in
theorem solution {A0 : Type} [Fintype A0] [DecidableEq A0]
    {L : Type} [Fintype L] [DecidableEq L]
    {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [Nonempty A0] [∀ i, Nonempty (Act i)]
    (u : L → A0 × ((i : L) → Act i) → ℝ) (hu : ∀ i a, |u i a| ≤ 1)
    (U : A0 × ((i : L) → Act i) → ℝ) (yt : A0 → ℝ) (xt : (i : L) → Act i → ℝ)
    (hNE : IsAuxNE u U yt xt) :
    otimes yt (AGT.profileProb xt) ∈ SNE u ∧
      ∀ c : A0, pairing U (otimes (pointMass c) (AGT.profileProb xt) -
        otimes yt (AGT.profileProb xt)) ≤ 0 := by
  refine ⟨subset_convexHull ℝ _ ⟨yt, xt, hNE.1, hNE.2.2, rfl⟩, ?_⟩
  intro c
  have hlot : AGT.IsLottery (pointMass c) := by
    refine ⟨fun a => ?_, ?_⟩
    · unfold pointMass; split_ifs <;> norm_num
    · unfold pointMass; simp
  have h := hNE.2.1 (pointMass c) hlot
  have hlin : ∀ (μ ν : A0 × ((i : L) → Act i) → ℝ),
      pairing U (μ - ν) = pairing U μ - pairing U ν := by
    intro μ ν
    unfold pairing
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [hlin]
  linarith
