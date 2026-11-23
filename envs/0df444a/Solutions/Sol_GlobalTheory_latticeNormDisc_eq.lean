-- Prove2me | solution 1 for GlobalTheory.latticeNormDisc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:49.644976+00:00
-- url     : https://prove2.me/submissions/a0c61705-8b04-4886-aa8b-351399ef206b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_latticeArea_eq_abs_im_mul_conj

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
theorem _root_.solution (L : PeriodPair) :
    latticeNormDisc L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 * ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ := by
  rw [latticeNormDisc, latticeArea_eq_abs_im_mul_conj]
end GlobalTheory
