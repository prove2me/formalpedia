-- Prove2me | solution 1 for GlobalTheory.isU_zero_shortIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:29.64835+00:00
-- url     : https://prove2.me/submissions/1941da84-bc7a-4e9a-8af1-9ca3d2bdf203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIndependentIsU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_zero_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
open GlobalTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace GlobalTheory
theorem _root_.solution (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 :=
  ⟨(IR I).zero_mem, fun a _ => by rw [inner_zero_left, Hf_im_zero_left]⟩
end GlobalTheory
