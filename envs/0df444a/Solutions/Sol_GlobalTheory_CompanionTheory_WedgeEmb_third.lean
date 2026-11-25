-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeEmb.third
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:29:44.406614+00:00
-- url     : https://prove2.me/submissions/c7469062-4aee-4d9e-84d3-bc120d4890b9

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorIntegrality
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_jW_er
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeEmb_sum_jW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeEmb
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.WedgeEmb
theorem _root_.solution : (jW n m)ᵀ * jW n m = ((m : ℂ) + 1) • (1 : Matrix (BranchingSupport.Sub n (m + 1)) (BranchingSupport.Sub n (m + 1)) ℂ) := by
  have h1 : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (-1) ^ (j : ℕ) = 1 := fun j => by
    rw [← mul_pow]
    norm_num
  ext I I'
  rw [Matrix.mul_apply]
  show ∑ p, jW n m p I * jW n m p I' = _
  have hs := sum_jW (fun p => jW n m p I') I
  rw [Finset.sum_congr rfl (fun p _ => mul_comm (jW n m p I) (jW n m p I')), hs]
  simp only [jW_er]
  by_cases h : I' = I
  · subst h
    have hc : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (if I' = I' then (-1) ^ (j : ℕ) else 0) = 1 :=
      fun j => by rw [if_pos rfl, h1]
    rw [Finset.sum_congr rfl (fun j _ => hc j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_num
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero, Matrix.smul_apply,
      Matrix.one_apply_ne (Ne.symm h), smul_zero]
end GlobalTheory.CompanionTheory.WedgeEmb
