-- Prove2me | solution 1 for MazurTransfer.ContinuousCoefficientExponentAndContinuity.quotient_continuousSMul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T01:32:23.741627+00:00
-- url     : https://prove2.me/submissions/ccdfd528-b5c8-4720-bf6d-1dcd4ea5b9a4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: surjective actual intertwiners give continuous actions on
their discrete coefficient targets, and exponent-nineteen coefficients give
the canonical F19 structure on continuous H1. Named downstream consumer:
the actual norm quotient H1 maps and local Selmer restriction diagrams.
-/
import Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientsData
import Theorems.Thm_MazurTransfer_discrete_equivariant_quotient_continuous_smul

noncomputable section
open MazurTransfer.RepresentationDiscreteCoefficients

theorem solution {k G V M : Type} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    [CommGroup M] [MulDistribMulAction G M] [Module k (Additive M)]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
    [IsTopologicalGroup M] [DiscreteTopology M] [ContinuousSMul G M]
    (ρ : Representation k G (Additive M)) (τ : Representation k G V)
    (f : Representation.IntertwiningMap ρ τ)
    (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m))
    (hf : Function.Surjective f) : ContinuousSMul G (Coefficient τ) := by
  exact MazurTransfer.discrete_equivariant_quotient_continuous_smul
    G M (Coefficient τ) (fromIntertwining ρ τ f) continuous_of_discreteTopology
    (fromIntertwining_surjective ρ τ f hf) (fromIntertwining_equivariant ρ τ f hρ)

#print axioms solution
