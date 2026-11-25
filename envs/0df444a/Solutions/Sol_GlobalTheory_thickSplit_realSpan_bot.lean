-- Prove2me | solution 1 for GlobalTheory.thickSplit_realSpan_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:42.717597+00:00
-- url     : https://prove2.me/submissions/458da0a3-365c-40c8-99a6-c4400f610776

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ThickSplitRealSpanBot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E]
    {dim : (E →+* ℂ) → ℕ} : IR (⊥ : Submodule ℤ (Vsp dim)) = ⊥ := by simp [IR]
end GlobalTheory
