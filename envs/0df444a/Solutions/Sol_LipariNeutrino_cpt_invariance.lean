-- Prove2me | solution 1 for LipariNeutrino.cpt_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:03:16.417722+00:00
-- url     : https://prove2.me/submissions/6ce12d2a-cf74-4127-8425-e95627ac0084

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

set_option autoImplicit false

open LipariNeutrino in
theorem solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m2 : Fin n → ℝ) (L E : ℝ)
    (α β : Fin n) :
    oscProb U m2 L E α β = oscProbBar U m2 L E β α := by
  unfold oscProbBar oscProb oscAmp
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, star_star]
  ring
#print axioms solution
