-- Prove2me | solution 1 for GeomQM.MomentumMap.mu_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:45:24.375624+00:00
-- url     : https://prove2.me/submissions/38f8ab85-5c89-4450-b14b-7bd78908d7ec

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

open Matrix

open GeomQM.MomentumMap in
theorem solution (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (ψ : Fin n → ℂ) :
    (momentumMap ψ).IsHermitian ∧
    momentumMap (U *ᵥ ψ) = U * momentumMap ψ * star U := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp [momentumMap, vecMulVec_apply, mul_comm]
  · ext i j
    simp only [momentumMap, vecMulVec_apply, mulVec, dotProduct, mul_apply, Matrix.star_apply,
      Pi.star_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
