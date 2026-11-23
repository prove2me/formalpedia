-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.single_mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:59.197958+00:00
-- url     : https://prove2.me/submissions/200a115f-9db5-4970-a88c-ef3fe544c8db

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
theorem _root_.solution (σ : L ≃ₐ[K] L) (a b : L) :
    (single σ a : CrossedProduct hf) * incl b = single σ (a * σ b) := by
  rw [incl_apply, single_mul_single, mul_one, map_one_snd_of_isMulCocycle₂ hf σ, val_smul_units,
    map_mul, mul_assoc, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]
end GroundTheory.Brauer.CrossedProduct
