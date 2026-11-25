-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.incl_eq_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:44.032331+00:00
-- url     : https://prove2.me/submissions/26c2e6a4-1ee6-45fd-b7ce-7a5d652fd0c1

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open groupCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
open GroundTheory.Brauer.CrossedProduct
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
variable {hf : IsMulCocycle₂ f}
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution (a : L) : (incl a : CrossedProduct hf) = a • 1 := by
  rw [incl_apply, one_def, smul_single]
end GroundTheory.Brauer.CrossedProduct
