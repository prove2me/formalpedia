-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.finrank_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:40.442706+00:00
-- url     : https://prove2.me/submissions/08e85cea-389c-477c-81c1-c67e918dc8a2

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_left

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
theorem _root_.solution [FiniteDimensional K L] [IsGalois K L] :
    Module.finrank K (CrossedProduct hf) = Module.finrank K L ^ 2 := by
  rw [← Module.finrank_mul_finrank K L (CrossedProduct hf), finrank_left,
    IsGalois.card_aut_eq_finrank, sq]
end GroundTheory.Brauer.CrossedProduct
