-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.basis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:34.159332+00:00
-- url     : https://prove2.me/submissions/bf4adda8-47e6-4aff-a234-86585d8e03d0

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
theorem _root_.solution (σ : L ≃ₐ[K] L) : (basis σ : CrossedProduct hf) = u σ := by
  rw [basis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  rfl
end GroundTheory.Brauer.CrossedProduct
