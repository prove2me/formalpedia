-- Prove2me | solution 1 for GroundTheory.LocalField.quasiCharExt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:52.360882+00:00
-- url     : https://prove2.me/submissions/4570ef12-c868-46fe-97d4-8639e1e18d18

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
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
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution (χ : Kˣ →* ℂˣ) (x y : K) :
    quasiCharExt χ (x * y) = quasiCharExt χ x * quasiCharExt χ y := by
  by_cases hx : x = 0
  · simp [quasiCharExt, hx]
  by_cases hy : y = 0
  · simp [quasiCharExt, hy]
  have : Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy := by
    ext
    simp
  simp only [quasiCharExt, mul_ne_zero hx hy, hx, hy, dif_neg, not_false_eq_true, this, map_mul,
    Units.val_mul]
end GroundTheory.LocalField
