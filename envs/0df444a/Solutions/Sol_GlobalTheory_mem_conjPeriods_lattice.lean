-- Prove2me | solution 1 for GlobalTheory.mem_conjPeriods_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:59.701909+00:00
-- url     : https://prove2.me/submissions/c5954f54-8ff9-469d-9327-c42b04bb3724

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (L : PeriodPair) (z : ℂ) :
    z ∈ (conjPeriods L).lattice ↔ starRingEnd ℂ z ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, conjPeriods]
  refine exists₂_congr fun m n => ⟨fun h => ?_, fun h => ?_⟩
  · simpa using congrArg (starRingEnd ℂ) h
  · simpa using congrArg (starRingEnd ℂ) h
end GlobalTheory
