-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.linearIndependent_of_kronecker_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:49:10.435169+00:00
-- url     : https://prove2.me/submissions/2d8d6b0a-1602-4f3f-b6b2-0c06ceebd7d5

import Mathlib.LinearAlgebra.LinearIndependent.Basic

theorem solution
    {K M ι : Type} [Field K] [AddCommMonoid M] [Module K M]
    [Fintype ι] [DecidableEq ι]
    (L : ι → M →ₗ[K] K) (v : ι → M)
    (h : ∀ i j, L i (v j) = if i = j then 1 else 0) :
    LinearIndependent K L := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro a b hab
  funext i
  have hEval := congrArg (fun f : M →ₗ[K] K => f (v i)) hab
  simpa [Fintype.linearCombination_apply, h] using hEval