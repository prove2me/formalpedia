-- Prove2me | solution 1 for GroundTheory.LocalField.mem_lowerRamificationGroupReal_of_lowerIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:24.501745+00:00
-- url     : https://prove2.me/submissions/b783bb0f-2bde-47c7-8edc-194ec20ed71a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_iff_lowerIndex


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
open ValuativeRel
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {t : ℝ} {σ σ' : L ≃ₐ[K] L}
    (h : σ ∈ lowerRamificationGroupReal K L t) (hle : lowerIndex K L σ ≤ lowerIndex K L σ') :
    σ' ∈ lowerRamificationGroupReal K L t := by
  rw [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_lowerIndex] at h ⊢
  exact h.trans hle
end GroundTheory.LocalField
