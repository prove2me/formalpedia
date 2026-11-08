-- Prove2me | solution 1 for MCAEndToEndMission.concentration_connectivity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:33:35.430168+00:00
-- url     : https://prove2.me/submissions/b6163765-b206-4f80-9203-7b6085c49cf5

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization

open scoped BigOperators

open Matrix

noncomputable section

theorem solution
    {n m : ℕ}
    (f : Fin n → (Fin m → ℝ) → ℝ)
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (N : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin n → ℝ)
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q, N.mulVec (fun k => MCAEndToEnd.rate f s q k) = 0)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hAinv : Ainv * (N * Matrix.diagonal p * MCAEndToEnd.elasticityDerivative f s p) = 1)
    (hp : ∀ k, p k ≠ 0)
    (hf0 : ∀ k, f k (s p) ≠ 0)
    (hs0 : ∀ i, s p i ≠ 0) :
    MCAEndToEnd.concentrationControl s p * MCAEndToEnd.elasticity f s p = -1 :=
  MCAEndToEnd.normalized_connectivity f s N p hf hs hsteady Ainv hAinv hp hf0 hs0
