-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.coeff_mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:15.304803+00:00
-- url     : https://prove2.me/submissions/284e30a9-d1fd-4f10-bb78-4f7e840b5065

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
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
theorem _root_.solution (x : CrossedProduct hf) (b : L) (σ : L ≃ₐ[K] L) :
    (x * incl b).coeff σ = x.coeff σ * σ b := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy]
  | single τ a =>
    rw [single_mul_incl, coeff_single, coeff_single]
    by_cases h : τ = σ
    · subst h; simp
    · simp [h]
end GroundTheory.Brauer.CrossedProduct
