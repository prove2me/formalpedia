-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.u_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:51.898573+00:00
-- url     : https://prove2.me/submissions/353c1fe4-783a-413a-ad79-d337fb44141a

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
theorem _root_.solution : (u 1 : CrossedProduct hf) = incl (f (1, 1) : L) := by
  rw [incl_apply, Units.mul_inv]; rfl
end GroundTheory.Brauer.CrossedProduct
