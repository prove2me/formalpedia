-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.u_mul_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:27.312351+00:00
-- url     : https://prove2.me/submissions/dc746ffc-0093-46d8-b7ba-1c818dce20ad

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
theorem _root_.solution (σ τ : L ≃ₐ[K] L) :
    (u σ : CrossedProduct hf) * u τ = incl (f (σ, τ) : L) * u (σ * τ) := by
  simp only [u]
  rw [single_mul_single, map_one, one_mul, one_mul, incl_mul_single, mul_one]
end GroundTheory.Brauer.CrossedProduct
