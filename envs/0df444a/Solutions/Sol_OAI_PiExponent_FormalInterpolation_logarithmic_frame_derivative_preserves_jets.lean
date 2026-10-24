-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:59:15.987069+00:00
-- url     : https://prove2.me/submissions/6065349f-9135-4e28-90c4-5bd9765d3006

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_derivative_preserves_jets_zero
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_derivative_preserves_jets_succ

open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (H : Real)
    (i : Fin (m + 1)) (hi : 0 < (v i : Real))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : logarithmicJetBound c v H F) :
    logarithmicJetBound c v (H - (v i : Real))
      (logarithmicFrameDerivative i F) := by
  cases i using Fin.cases with
  | zero =>
      exact logarithmic_frame_derivative_preserves_jets_zero
        c v H hi F hjet
  | succ j =>
      exact logarithmic_frame_derivative_preserves_jets_succ
        c v H j hi F hjet