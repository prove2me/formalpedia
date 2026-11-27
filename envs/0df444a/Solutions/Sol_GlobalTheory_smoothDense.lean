-- Prove2me | solution 1 for GlobalTheory.smoothDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:27.121994+00:00
-- url     : https://prove2.me/submissions/021628c8-0fb9-4b39-af10-60a7e7d40605

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SmoothDense
import Theorems.Thm_P2M_GlobalTheory_smooth_smoothLocus___comp_f25dce1b6b4e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : SmoothDenseSt := by
  intro K _ _ X f hX hf
  have : LocallyOfFinitePresentation f := inferInstance
  exact f.dense_smoothLocus_of_perfectField.mono
    fun x hx => ⟨f.smoothLocus, hx, smooth_smoothLocus_ι_comp f⟩
end GlobalTheory
