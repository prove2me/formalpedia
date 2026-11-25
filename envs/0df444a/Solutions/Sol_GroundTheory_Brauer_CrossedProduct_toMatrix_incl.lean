-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.toMatrix_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:17.072628+00:00
-- url     : https://prove2.me/submissions/81a177ed-c298-47c2-b5b1-fca3de3b2829

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
theorem _root_.solution (a : L) :
    toMatrix j hf (incl a) = diagHom (fun ρ => j.comp (ρ⁻¹ : L ≃ₐ[K] L).toAlgHom) a :=
  lift_incl _ _ _ _ _ a
end GroundTheory.Brauer.CrossedProduct
