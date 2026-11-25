-- Prove2me | solution 1 for GroundTheory.LocalField.indicator_valBall_mem_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:28.679657+00:00
-- url     : https://prove2.me/submissions/b3026aff-2432-419c-9b5e-3c4ded050364

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_isLocallyConstant_of_add_valBall
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
namespace GroundTheory.LocalField
theorem _root_.solution (k : ℤ) :
    (valBall K k : Set K).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat K := by
  refine ⟨isLocallyConstant_of_add_valBall (N := k) fun x h hh => ?_, ?_⟩
  · have hiff : x + h ∈ valBall K k ↔ x ∈ valBall K k :=
      ⟨fun h' => by simpa using sub_mem h' hh, fun h' => add_mem h' hh⟩
    by_cases hx : x ∈ valBall K k
    · rw [Set.indicator_of_mem (show x + h ∈ (valBall K k : Set K) from hiff.mpr hx),
        Set.indicator_of_mem (show x ∈ (valBall K k : Set K) from hx)]
    · rw [Set.indicator_of_notMem (show x + h ∉ (valBall K k : Set K) from mt hiff.mp hx),
        Set.indicator_of_notMem (show x ∉ (valBall K k : Set K) from hx)]
  · exact HasCompactSupport.intro (isCompact_valBall k) fun x hx => Set.indicator_of_notMem hx _
end GroundTheory.LocalField
