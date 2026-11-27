-- Prove2me | solution 1 for GlobalTheory.WModel.wModel_p_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:13.310496+00:00
-- url     : https://prove2.me/submissions/52b404cc-91e7-4339-8514-b049eae4e66c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_WFrobStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZmodPrimeSqLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 TrivSqZeroExt
open GlobalTheory GlobalTheory.WModel
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.WModel
theorem _root_.solution : (p : ((wModel p).W : Type)) ≠ 0 := by
  intro h
  have h1 : (p : ZMod (p ^ 2)) * 1 = 0 := by rw [mul_one]; exact h
  rw [ann_p, map_one] at h1
  exact one_ne_zero h1
end GlobalTheory.WModel
