-- Prove2me | solution 1 for GroundTheory.LocalField.eq_of_isClassFun_of_charInner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:17:28.538904+00:00
-- url     : https://prove2.me/submissions/3a345571-2d34-481f-8fa9-46062acfb16e

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
theorem _root_.solution {f f' : G → ℂ} (hf : IsClassFun f) (hf' : IsClassFun f')
    (h : ∀ ψ ∈ irrChars G, charInner G f ψ = charInner G f' ψ) : f = f' := by
  rw [eq_sum_irrChars_of_isClassFun hf, eq_sum_irrChars_of_isClassFun hf']
  exact Finset.sum_congr rfl fun ψ hψ ↦ by rw [h ψ hψ]
end GroundTheory.LocalField
