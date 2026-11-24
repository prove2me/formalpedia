-- Prove2me | solution 1 for GlobalTheory.latticeNormDisc_conjPeriods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:12:57.348832+00:00
-- url     : https://prove2.me/submissions/0cdfd387-b461-47a7-b4a1-9ecda726caf4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_latticeArea_eq_abs_im_mul_conj
import Theorems.Thm_GlobalTheory_G_conjPeriods

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
    latticeNormDisc (conjPeriods L) = latticeNormDisc L := by
  have e : (conjPeriods L).g₂ ^ 3 - 27 * (conjPeriods L).g₃ ^ 2 =
      starRingEnd ℂ (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    simp only [PeriodPair.g₂, PeriodPair.g₃, G_conjPeriods, map_sub, map_mul, map_pow, map_ofNat]
  have a : latticeArea (conjPeriods L) = latticeArea L := by
    rw [latticeArea_eq, latticeArea_eq_abs_im_mul_conj]
    simp [conjPeriods]
  rw [latticeNormDisc, latticeNormDisc, e, a, Complex.norm_conj]
end GlobalTheory
