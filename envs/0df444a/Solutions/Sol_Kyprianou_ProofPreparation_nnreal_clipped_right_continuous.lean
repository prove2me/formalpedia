-- Prove2me | solution 1 for Kyprianou.ProofPreparation.nnreal_clipped_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:04:01.003223+00:00
-- url     : https://prove2.me/submissions/81b6e798-8de2-42d4-9cdc-d6798e5b416b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Set Topology
open scoped Topology NNReal ENNReal
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem nnreal_clipped_right_continuous
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t) :
    ∀ u : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => f (min (v : ℝ) 1)) (Set.Ici u) u := by
  intro u
  have ht : min (u : ℝ) 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨le_min u.2 zero_le_one, min_le_right _ _⟩
  have hg : ContinuousWithinAt (fun v : ℝ≥0 => min (v : ℝ) 1) (Set.Ici u) u :=
    (NNReal.continuous_coe.min continuous_const).continuousWithinAt
  refine ContinuousWithinAt.comp (g := f) (hR _ ht) hg ?_
  intro v hv
  simp only [Set.mem_Ici] at hv
  exact ⟨min_le_min (NNReal.coe_le_coe.2 hv) le_rfl, min_le_right _ _⟩

end Kyprianou.ProofPreparation

theorem solution
    (f : ℝ → ℝ)
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContinuousWithinAt f (Set.Icc t 1) t) :
    ∀ u : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => f (min (v : ℝ) 1)) (Set.Ici u) u := by
  first
  | exact Kyprianou.ProofPreparation.nnreal_clipped_right_continuous
  | exact Kyprianou.ProofPreparation.nnreal_clipped_right_continuous ..
  | (apply Kyprianou.ProofPreparation.nnreal_clipped_right_continuous <;> assumption)
