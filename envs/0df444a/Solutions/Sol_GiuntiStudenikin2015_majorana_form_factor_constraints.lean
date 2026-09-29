-- Prove2me | solution 1 for GiuntiStudenikin2015.majorana_form_factor_constraints
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:24:33.137656+00:00
-- url     : https://prove2.me/submissions/dcc5626c-4795-4279-ba6b-49b25049a749

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

set_option autoImplicit false

open GiuntiStudenikin2015 in
theorem solution {N : ℕ} (f : Matrix (Fin N) (Fin N) ℂ)
    (hf : f.IsHermitian) :
    (f.transpose = -f → (∀ i, f i i = 0) ∧ f.map star = -f) ∧
    (f.transpose = f → f.map star = f) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have key : ∀ i j, f j i = -f i j := by
      intro i j
      have := congrFun (congrFun h i) j
      simpa [Matrix.transpose_apply, Matrix.neg_apply] using this
    refine ⟨fun i => ?_, ?_⟩
    · have hi := key i i
      linear_combination hi / 2
    · ext i j
      rw [Matrix.map_apply, Matrix.neg_apply, hf.apply j i, key]
  · ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.transpose_apply] at this
    rw [Matrix.map_apply, hf.apply j i, this]
#print axioms solution
