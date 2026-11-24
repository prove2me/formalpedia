-- Prove2me | solution 1 for GlobalTheory.G_conjPeriods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:14.064248+00:00
-- url     : https://prove2.me/submissions/eb7b4c90-7a43-4354-bc20-c4fecd70c704

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_mem_conjPeriods_lattice

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
theorem _root_.solution (L : PeriodPair) (n : ℕ) :
    (conjPeriods L).G n = starRingEnd ℂ (L.G n) := by
  let e : L.lattice ≃ (conjPeriods L).lattice :=
    { toFun := fun x => ⟨starRingEnd ℂ x, (mem_conjPeriods_lattice L _).2 (by simp)⟩
      invFun := fun y => ⟨starRingEnd ℂ y, (mem_conjPeriods_lattice L _).1 y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  simp only [PeriodPair.G]
  rw [← e.tsum_eq, Complex.conj_tsum]
  simp [e]
end GlobalTheory
