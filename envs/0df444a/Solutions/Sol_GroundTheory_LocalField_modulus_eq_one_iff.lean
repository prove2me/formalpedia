-- Prove2me | solution 1 for GroundTheory.LocalField.modulus_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:18.185573+00:00
-- url     : https://prove2.me/submissions/3d37d72a-dbb1-4a1c-934d-d4ab39c0a580

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard_nnreal
import Theorems.Thm_GroundTheory_LocalField_modulus_of_ne_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {x : K} : modulus x = 1 ↔ x ≠ 0 ∧ ord x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [modulus_of_ne_zero hx, ← zpow_zero (residueCard K : ℝ≥0),
    (zpow_right_strictMono₀ one_lt_residueCard_nnreal).injective.eq_iff]
  simp [hx]
end GroundTheory.LocalField
