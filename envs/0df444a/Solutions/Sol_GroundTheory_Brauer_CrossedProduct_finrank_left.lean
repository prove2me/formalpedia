-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.finrank_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:16.109312+00:00
-- url     : https://prove2.me/submissions/bc91a4b4-9e8a-4801-bb30-eca805d399e8

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
theorem _root_.solution [FiniteDimensional K L] :
    Module.finrank L (CrossedProduct hf) = Nat.card (L ≃ₐ[K] L) :=
  Module.finrank_eq_nat_card_basis basis
end GroundTheory.Brauer.CrossedProduct
