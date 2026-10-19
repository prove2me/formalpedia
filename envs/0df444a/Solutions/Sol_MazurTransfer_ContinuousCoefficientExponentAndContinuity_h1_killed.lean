-- Prove2me | solution 1 for MazurTransfer.ContinuousCoefficientExponentAndContinuity.h1_killed
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T01:31:58.795997+00:00
-- url     : https://prove2.me/submissions/7d7f8115-d8c4-484e-b288-6ed3f789a028

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: surjective actual intertwiners give continuous actions on
their discrete coefficient targets, and exponent-nineteen coefficients give
the canonical F19 structure on continuous H1. Named downstream consumer:
the actual norm quotient H1 maps and local Selmer restriction diagrams.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData

noncomputable section
open MazurTransfer.ContinuousFirstCohomologyPresentation

theorem solution (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (n : ℕ) (h : ∀ m : M, m ^ n = 1) (x : H1 G M) : n • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro z
  have hz : n • z = 0 := by
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    change (Additive.toMul (z.val g) : M) ^ n = 1
    exact h _
  change n • classMap G M z = 0
  rw [← map_nsmul, hz, map_zero]


#print axioms solution
