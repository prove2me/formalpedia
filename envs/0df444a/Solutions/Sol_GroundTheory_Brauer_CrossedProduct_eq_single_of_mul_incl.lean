-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.eq_single_of_mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:38.531838+00:00
-- url     : https://prove2.me/submissions/b6776677-7ac4-4c66-84c4-e6551a5ff019

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_u


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
universe u v
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution (σ : L ≃ₐ[K] L) (x : CrossedProduct hf)
    (hx : ∀ b : L, x * incl b = incl (σ b) * x) : x = single σ (x.coeff σ) := by
  have hzero : ∀ τ, τ ≠ σ → x.coeff τ = 0 := by
    intro τ hτ
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ τ b := by
      by_contra h
      push Not at h
      exact hτ (AlgEquiv.ext fun b => (h b).symm)
    have h : (incl (σ b) * x - x * incl b).coeff τ = 0 := by
      rw [hx b, sub_self]
      rfl
    rw [coeff_incl_mul_sub_mul_incl] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hb)
  rw [← incl_mul_u]
  exact eq_incl_mul_u_of_coeff_eq_zero x σ hzero
end GroundTheory.Brauer.CrossedProduct
