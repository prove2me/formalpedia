-- Prove2me | solution 1 for GlobalTheory.IsHomothetic.latticeNormDisc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:46.346196+00:00
-- url     : https://prove2.me/submissions/eaf5ff86-2ade-4f71-9a05-074a6f585186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_P2M_GlobalTheory_IsHomothetic_g__eq_8571fef95872
import Theorems.Thm_P2M_GlobalTheory_IsHomothetic_g__eq_dbfeb170147e


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
namespace IsHomothetic
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeNormDisc L' = latticeNormDisc L := by
  have hc : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 h.ne_zero
  have e : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h.g₂_eq, h.g₃_eq]
    ring
  rw [latticeNormDisc, latticeNormDisc, h.latticeArea_eq, e, norm_mul, norm_inv, norm_pow]
  field_simp
end IsHomothetic
end GlobalTheory
