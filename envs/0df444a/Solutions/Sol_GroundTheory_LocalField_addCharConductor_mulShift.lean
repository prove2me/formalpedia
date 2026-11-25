-- Prove2me | solution 1 for GroundTheory.LocalField.addCharConductor_mulShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:24.02883+00:00
-- url     : https://prove2.me/submissions/86f2b5fd-f8aa-4367-9306-e2b66dec45e4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Theorems.Thm_GroundTheory_LocalField_mulShift_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter
open scoped WithZero Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (ψ : AddChar K Circle)
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
namespace GroundTheory.LocalField
theorem _root_.solution {a : K} (ha : a ≠ 0) :
    addCharConductor (ψ.mulShift a) = addCharConductor ψ - ord a := by
  have hc := continuous_mulShift hψ a
  have h1 := mulShift_ne_one hψ1 ha
  have key : ∀ n, addCharConductor (ψ.mulShift a) ≤ n ↔ addCharConductor ψ - ord a ≤ n := fun n => by
    rw [← isTrivialOn_iff hc h1, isTrivialOn_mulShift_iff ha, isTrivialOn_iff hψ hψ1]
    omega
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)
end GroundTheory.LocalField
