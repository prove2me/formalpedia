-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicFrameWord_preserves_degree_bound_of_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:53:19.692016+00:00
-- url     : https://prove2.me/submissions/06e94e9f-0844-4d3a-b769-27002c2746d0

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hstep : ∀ (i : Fin (m + 1)) (F : MvPolynomial (Fin (m + 1)) Complex),
      logarithmicDegreeBound w H F →
        logarithmicDegreeBound w H (logarithmicFrameDerivative i F))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F)
    (word : List (Fin (m + 1))) :
    logarithmicDegreeBound w H (logarithmicFrameWord word F) := by
  induction word with
  | nil =>
      simpa [logarithmicFrameWord] using hF
  | cons i word ih =>
      simpa [logarithmicFrameWord] using
        hstep i (logarithmicFrameWord word F) ih