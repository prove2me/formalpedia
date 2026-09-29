-- Prove2me | solution 1 for NewtonGravitation.pointForce_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:16:51.974982+00:00
-- url     : https://prove2.me/submissions/51e66710-6e19-496e-89fc-fa3f6a4c03f9

import Definitions.Def_NewtonGravitation_Defs

theorem solution (m₁ m₂ : ℝ) (r₁ r₂ : NewtonGravitation.Space) :
    NewtonGravitation.pointForce m₂ m₁ r₂ r₁ =
      -NewtonGravitation.pointForce m₁ m₂ r₁ r₂ := by
  unfold NewtonGravitation.pointForce
  have hs : r₁ - r₂ = -(r₂ - r₁) := by abel
  have hn : ‖r₁ - r₂‖ = ‖r₂ - r₁‖ := by rw [hs, norm_neg]
  rw [hn, hs]
  simp only [smul_neg, smul_smul]
  congr 1
  ring_nf

#print axioms solution
