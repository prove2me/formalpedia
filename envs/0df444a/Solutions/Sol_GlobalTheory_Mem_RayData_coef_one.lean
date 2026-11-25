-- Prove2me | solution 1 for GlobalTheory.Mem.RayData.coef_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:43.857485+00:00
-- url     : https://prove2.me/submissions/7f0c93e4-4ec1-483a-9b79-3d7c51a28aa2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Theorems.Thm_GlobalTheory_Mem_RayData_cnt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem
open NumberField IsDedekindDomain
attribute [instance] RayData.grp RayData.fin
open GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Mem.RayData
theorem _root_.solution (χ : D.G →* ℂˣ) : D.coef χ 1 = 1 := by
  rw [coef, Finset.sum_eq_single (1 : D.G)]
  · rw [D.cnt_one, if_pos rfl, map_one, Units.val_one, mul_one]
  · intro b _ hb
    rw [D.cnt_one, if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.Mem.RayData
