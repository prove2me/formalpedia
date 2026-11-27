-- Prove2me | solution 2 for GroundTheory.Brauer.CrossedProduct.coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:31.607116+00:00
-- url     : https://prove2.me/submissions/3f2a0131-62ed-4c5e-9d69-345579f05210

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
theorem _root_.solution :
    (1 : CrossedProduct hf).coeff = Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L) := rfl
end GroundTheory.Brauer.CrossedProduct
