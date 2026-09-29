-- Prove2me | solution 1 for LipariNeutrino.diagonal_cp_conserving
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:03:27.935127+00:00
-- url     : https://prove2.me/submissions/2412e0a8-9fef-4d73-bce0-fdd6f35ba158

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

set_option autoImplicit false

open LipariNeutrino in
theorem solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m2 : Fin n → ℝ)
    (L E : ℝ) (α : Fin n) :
    oscProbBar U m2 L E α α = oscProb U m2 L E α α := by
  unfold oscProbBar oscProb oscAmp
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, star_star]
  ring
#print axioms solution
