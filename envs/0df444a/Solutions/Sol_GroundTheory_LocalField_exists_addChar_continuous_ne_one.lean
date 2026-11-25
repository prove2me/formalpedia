-- Prove2me | solution 1 for GroundTheory.LocalField.exists_addChar_continuous_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:27:32.09522+00:00
-- url     : https://prove2.me/submissions/14cd340a-eefc-4bf1-867e-ce08bf1a7d98

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Theorems.Thm_GroundTheory_LocalField_exists_addChar_addCharConductor_eq_zero

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
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hc, hne, -⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  exact ⟨ψ, hc, hne⟩
end GroundTheory.LocalField
