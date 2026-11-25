-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.isUnit_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:46:49.267088+00:00
-- url     : https://prove2.me/submissions/307ed10f-5b2a-4540-a0e0-b86df043e0e2

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_incl
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_u
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_one

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
theorem _root_.solution (σ : L ≃ₐ[K] L) : IsUnit (u σ : CrossedProduct hf) := by
  have h := smul_map_inv_div_map_inv_of_isMulCocycle₂ hf σ
  rw [map_one_snd_of_isMulCocycle₂ hf σ, div_eq_div_iff_mul_eq_mul] at h
  have hr : σ • (f (σ⁻¹, σ) * f (1, 1))⁻¹ * (f (σ, σ⁻¹) * f (1, 1)) = 1 := by
    rw [smul_inv', smul_mul', inv_mul_eq_one, h, mul_comm]
  have hl : (f (σ⁻¹, σ) * f (1, 1))⁻¹ * (f (σ⁻¹, σ) * f (1, 1)) = 1 := inv_mul_cancel _
  refine isUnit_iff_exists.2
    ⟨incl (((f (σ⁻¹, σ) * f (1, 1))⁻¹ : Lˣ) : L) * u σ⁻¹, ?_, ?_⟩
  · rw [← mul_assoc, u_mul_incl, mul_assoc, u_mul_u, mul_inv_cancel, u_one, ← map_mul, ← map_mul,
      ← val_smul_units, ← Units.val_mul, ← Units.val_mul, hr, Units.val_one, map_one]
  · rw [mul_assoc, u_mul_u, inv_mul_cancel, u_one, ← map_mul, ← map_mul, ← Units.val_mul,
      ← Units.val_mul, hl, Units.val_one, map_one]
end GroundTheory.Brauer.CrossedProduct
