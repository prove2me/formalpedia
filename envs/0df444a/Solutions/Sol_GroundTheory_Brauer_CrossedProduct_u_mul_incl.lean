-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.u_mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:06.441828+00:00
-- url     : https://prove2.me/submissions/e952cde0-1f13-4020-9fea-a741e38c5ae2

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_single
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_single_mul_incl

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
theorem _root_.solution (σ : L ≃ₐ[K] L) (a : L) :
    (u σ : CrossedProduct hf) * incl a = incl (σ a) * u σ := by
  simp only [u]
  rw [single_mul_incl, one_mul, incl_mul_single, mul_one]
end GroundTheory.Brauer.CrossedProduct
