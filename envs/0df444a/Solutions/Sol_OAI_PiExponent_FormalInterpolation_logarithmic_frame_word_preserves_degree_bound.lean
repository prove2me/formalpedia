-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:49:54.706551+00:00
-- url     : https://prove2.me/submissions/dbc52a11-6927-4032-a3fe-945bdc8463c9

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameDerivative_preserves_degree_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicFrameWord_preserves_degree_bound_of_step

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F)
    (word : List (Fin (m + 1))) :
    logarithmicDegreeBound w H (logarithmicFrameWord word F) := by
  apply logarithmicFrameWord_preserves_degree_bound_of_step w H
    (fun i P hP => logarithmicFrameDerivative_preserves_degree_bound w H hw i P hP)
    F hF word