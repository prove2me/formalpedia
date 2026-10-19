-- Prove2me | solution 1 for MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restriction_classMap_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T00:28:24.357927+00:00
-- url     : https://prove2.me/submissions/f887874b-5ca1-4fcf-b080-1f5d9b8fbd31

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restriction of continuous cocycles descends to continuous
H1 for every subgroup with its induced topology. A restricted class is
zero precisely when the restricted cocycle is a subgroup coboundary.
Named downstream consumer: local conditions on actual norm Kummer classes.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologySubgroupRestrictionData
noncomputable section
open MazurTransfer.ContinuousFirstCohomologyPresentation
open MazurTransfer.ContinuousFirstCohomologySubgroupRestriction
theorem solution (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (S : Subgroup G) (z : continuousCocycles G M) :
    restriction G M S (classMap G M z) = 0 ↔
      ∃ m : M, ∀ s : S, s • m / m = (Additive.toMul (z.val s.val) : M) := by
  rw [restriction_classMap, classMap_eq_zero_iff]
  constructor
  · intro h
    exact groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
      (fun s : S => (Additive.toMul (z.val s.val) : M)) h
  · intro h
    exact (groupCohomology.coboundariesOfIsMulCoboundary₁ h).property

#print axioms solution
