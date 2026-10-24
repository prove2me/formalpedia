-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_word_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:31:50.285345+00:00
-- url     : https://prove2.me/submissions/1b34b43e-00c3-4af8-80dc-6427939faeaa

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContactSupportBound_pderiv

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound W N F)
    (word : List (Fin m))
    (hW : ∀ i, 0 ≤ (W i : Real)) :
    fibreContactSupportBound W N (fibreContactWord word F) := by
  revert F hF
  induction word with
  | nil =>
      intro F hF
      simpa [fibreContactWord] using hF
  | cons i word ih =>
      intro F hF
      change fibreContactSupportBound W N
        (MvPolynomial.pderiv i (fibreContactWord word F))
      exact fibreContactSupportBound_pderiv W N
        (fibreContactWord word F) (ih F hF) i hW