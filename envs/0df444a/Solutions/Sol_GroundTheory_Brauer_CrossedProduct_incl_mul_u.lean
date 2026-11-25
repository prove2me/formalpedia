-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.incl_mul_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:40.091033+00:00
-- url     : https://prove2.me/submissions/02407690-a16b-4a3f-988c-c7a809e37225

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_single

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
theorem _root_.solution (a : L) (σ : L ≃ₐ[K] L) : (incl a : CrossedProduct hf) * u σ = single σ a := by
  rw [u, incl_mul_single, mul_one]
end GroundTheory.Brauer.CrossedProduct
