-- Prove2me | solution 1 for LipariNeutrino.jarlskogCoeff_symmetries
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:03:16.285759+00:00
-- url     : https://prove2.me/submissions/2b495b24-3ce8-43a5-9592-856e2155520c

import Mathlib
import Definitions.Def_LipariNeutrino_OscillationProbability

set_option autoImplicit false

open LipariNeutrino in
theorem solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (α β j k : Fin n) :
    jarlskogCoeff U α β j k = -jarlskogCoeff U α β k j ∧
    jarlskogCoeff U α β j k = -jarlskogCoeff U β α j k ∧
    jarlskogCoeff U α β j j = 0 ∧
    jarlskogCoeff U α α j k = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [jarlskogCoeff, Complex.mul_im, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
#print axioms solution
