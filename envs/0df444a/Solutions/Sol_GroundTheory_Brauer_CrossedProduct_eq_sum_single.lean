-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.eq_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:34.427965+00:00
-- url     : https://prove2.me/submissions/76a92525-f734-45ea-885b-63285da6ca01

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
theorem _root_.solution (x : CrossedProduct hf) :
    x = x.coeff.sum fun σ a => single σ a := by
  apply coeff_injective
  change x.coeff = coeffAddHom (x.coeff.sum fun σ a => single σ a)
  rw [map_finsuppSum]
  exact (Finsupp.sum_single x.coeff).symm
end GroundTheory.Brauer.CrossedProduct
