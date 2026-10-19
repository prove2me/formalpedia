-- Prove2me | solution 1 for MazurTransfer.ContinuousFirstCohomologyCoefficientMap.restriction_coefficientMap
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T00:28:32.759359+00:00
-- url     : https://prove2.me/submissions/c75f56c9-8dd1-4280-939c-97f5191eac4d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous equivariant coefficient homomorphisms induce
maps on the EXISTING continuous-cocycle H1 presentation and commute with
restriction to every subgroup. Named downstream consumer: the actual
arithmetic norm-character Kummer images and local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoefficientMapData
noncomputable section
open MazurTransfer.ContinuousFirstCohomologyPresentation
open MazurTransfer.ContinuousFirstCohomologySubgroupRestriction
open MazurTransfer.ContinuousFirstCohomologyCoefficientMap
theorem solution (G M N : Type) [Group G] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [IsTopologicalGroup M] [IsTopologicalGroup N]
  (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (hc : Continuous f) (S : Subgroup G) (x : H1 G M) :
    restriction G N S (coefficientMap G M N f hf hc x) =
      coefficientMap S M N f (fun s m => hf s.val m) hc (restriction G M S x) := by
  refine Quotient.inductionOn x ?_
  intro z
  change classMap S N (restrictContinuousCocycles G N S (mapContinuousCocycles G M N f hf hc z)) =
    classMap S N (mapContinuousCocycles S M N f (fun s m => hf s.val m) hc
      (restrictContinuousCocycles G M S z))
  apply congrArg (classMap S N)
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro s
  rfl

#print axioms solution
