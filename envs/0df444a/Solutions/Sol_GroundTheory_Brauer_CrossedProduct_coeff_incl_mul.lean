-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.coeff_incl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:24.674869+00:00
-- url     : https://prove2.me/submissions/09209911-3c10-4c84-81dd-c8919d5075ce

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul

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
theorem _root_.solution (b : L) (x : CrossedProduct hf) (σ : L ≃ₐ[K] L) :
    (incl b * x).coeff σ = b * x.coeff σ := by
  rw [incl_mul, coeff_smul, Finsupp.smul_apply, smul_eq_mul]
end GroundTheory.Brauer.CrossedProduct
