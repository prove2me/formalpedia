-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_isClassFun_of_charInner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:12.756008+00:00
-- url     : https://prove2.me/submissions/c15047ba-7c87-41d9-bb8e-7f8c501ffd57

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_eq_sum_irrChars_of_isClassFun

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
open Module Representation
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution {f : G → ℂ} (hf : IsClassFun f)
    (h : ∀ ψ ∈ irrChars G, charInner G f ψ = 0) : f = 0 := by
  rw [eq_sum_irrChars_of_isClassFun hf]
  exact Finset.sum_eq_zero fun ψ hψ ↦ by rw [h ψ hψ, zero_smul]
end GroundTheory.LocalField
