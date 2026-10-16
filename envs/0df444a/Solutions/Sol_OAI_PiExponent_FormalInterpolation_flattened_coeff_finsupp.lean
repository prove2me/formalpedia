-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:39:05.789245+00:00
-- url     : https://prove2.me/submissions/25c1ea94-6a78-4665-880a-c1ed5c31ae51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_flattened_coeff_finsupp_monomial

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (F : MvPolynomial (Fin m) (Polynomial Complex))
    (e : Fin (m + 1) →₀ Nat) :
    (MvPolynomial.eval₂Hom
      (((Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) :
        Polynomial Complex →ₐ[Complex] MvPolynomial (Fin (m + 1)) Complex).toRingHom)
      (fun i : Fin m => MvPolynomial.X i.succ) F).coeff e =
      ((F.coeff (InterpolationMatrix.exponentVector (fun i => e i.succ))).coeff (e 0)) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial d p =>
      exact OAI.PiExponent.FormalInterpolation.flattened_coeff_finsupp_monomial p d e
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.coeff_add, Polynomial.coeff_add,
        ← MvPolynomial.coe_eval₂Hom, hP, hQ]