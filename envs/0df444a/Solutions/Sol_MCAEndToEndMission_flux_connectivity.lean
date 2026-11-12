-- Prove2me | solution 1 for MCAEndToEndMission.flux_connectivity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:50:21.379513+00:00
-- url     : https://prove2.me/submissions/39a323c3-1c9d-4715-b22e-7814cefaa57e

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization
open scoped BigOperators
open Matrix

noncomputable section
theorem solution
    {n m q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → (Fin m → ℝ) → ℝ)
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (N : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin n → ℝ)
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hsteady : ∀ q', N.mulVec (fun k => MCAEndToEnd.rate f s q' k) = 0)
    (Ainv : Matrix (Fin m) (Fin m) ℝ)
    (hAinv : Ainv * (N * Matrix.diagonal p * MCAEndToEnd.elasticityDerivative f s p) = 1)
    (hp : ∀ k, p k ≠ 0)
    (hf0 : ∀ k, f k (s p) ≠ 0)
    (hJ0 : ∀ r, MCAEndToEnd.flux R f s p r ≠ 0) :
    ∀ r j, ∑ l, MCAEndToEnd.fluxControl R f s p r l * MCAEndToEnd.elasticity f s p l j = 0 :=
  MCAEndToEnd.flux_connectivity (f := f) (s := s) (N := N) (R := R) (p := p)
    hf hs hsteady Ainv hAinv hp hf0 hJ0
end
