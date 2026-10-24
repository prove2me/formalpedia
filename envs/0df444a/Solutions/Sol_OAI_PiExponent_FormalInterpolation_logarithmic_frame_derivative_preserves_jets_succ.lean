-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_frame_derivative_preserves_jets_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:04:11.637694+00:00
-- url     : https://prove2.me/submissions/2de33773-88f0-4f1d-82c0-573e2c21dd3a

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_pderiv_succ
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicJetBound_pderiv_of_commutes

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (H : Real) (i : Fin m)
    (hi : 0 < (v i.succ : Real)) (F : MvPolynomial (Fin (m + 1)) Complex)
    (hjet : logarithmicJetBound c v H F) :
    logarithmicJetBound c v (H - (v i.succ : Real))
      (logarithmicFrameDerivative i.succ F) := by
  change logarithmicJetBound c v (H - (v i.succ : Real))
    (MvPolynomial.pderiv i.succ F)
  simpa only [logarithmicJetBound] using
    OAI.PiExponent.FormalInterpolation.logarithmicJetBound_pderiv_of_commutes
      (φ := fun j => formalJet (c j)) v H i F
      (by simpa only [logarithmicJetBound] using hjet)
      (by
        intro j
        exact OAI.PiExponent.FormalInterpolation.formalJet_pderiv_succ (c j) i F)