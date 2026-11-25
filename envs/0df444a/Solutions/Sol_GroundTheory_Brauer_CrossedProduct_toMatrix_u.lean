-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.toMatrix_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:58.167215+00:00
-- url     : https://prove2.me/submissions/bcab4530-608f-43a4-8547-c873d23e8ba9

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductRegular

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
open groupCohomology TensorProduct
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [DecidableEq (L ≃ₐ[K] L)]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
variable {C : Type*} [Ring C] [Algebra K C] (j : L →ₐ[K] C)
variable (hf : IsMulCocycle₂ f)
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution (σ : L ≃ₐ[K] L) : toMatrix j hf (u σ) = regularU j f σ :=
  lift_u _ _ _ _ _ σ
end GroundTheory.Brauer.CrossedProduct
