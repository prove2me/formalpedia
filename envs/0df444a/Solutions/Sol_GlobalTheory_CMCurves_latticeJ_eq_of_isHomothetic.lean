-- Prove2me | solution 1 for GlobalTheory.CMCurves.latticeJ_eq_of_isHomothetic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:54.987066+00:00
-- url     : https://prove2.me/submissions/0cd98444-7228-46d5-8667-0d0458b7b4c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Theorems.Thm_P2M_GlobalTheory_IsHomothetic_g__eq_8571fef95872
import Theorems.Thm_P2M_GlobalTheory_IsHomothetic_g__eq_dbfeb170147e
import Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
open GlobalTheory
open GlobalTheory.CMCurves
namespace GlobalTheory.CMCurves
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeJ L' = latticeJ L := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact L.ω₁_div_two_notMem_lattice ((h _).1 (by simp))
  have hd := g₂_cube_sub_g₃_sq_ne_zero L
  have hd' := g₂_cube_sub_g₃_sq_ne_zero L'
  unfold latticeJ
  rw [h.g₂_eq, h.g₃_eq] at hd' ⊢
  rw [div_eq_div_iff hd' hd]
  ring
end GlobalTheory.CMCurves
