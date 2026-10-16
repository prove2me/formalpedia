-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.flattened_coeff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:32:22.221637+00:00
-- url     : https://prove2.me/submissions/e6153cf7-81fd-4970-9f2b-a6d0f7b0e9f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_flattened_coeff_finsupp

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (F : MvPolynomial (Fin m) (Polynomial Complex))
    (a : Fin (m + 1) → Nat) :
    (MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ) F).coeff
        (InterpolationMatrix.exponentVector a) =
      ((F.coeff (InterpolationMatrix.exponentVector (fun i => a i.succ))).coeff (a 0)) := by
  simpa [InterpolationMatrix.exponentVector] using
    OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp
      (m := m) F (InterpolationMatrix.exponentVector a)