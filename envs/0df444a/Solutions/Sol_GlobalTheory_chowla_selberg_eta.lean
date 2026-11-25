-- Prove2me | solution 1 for GlobalTheory.chowla_selberg_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:33.132512+00:00
-- url     : https://prove2.me/submissions/0da4b88c-af57-41f0-ba99-014bed9aab94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_LFunction_one_and_mean_log_eta
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
  {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) (σ : K →+* ℂ)
include h2 hD hd hχ
namespace GlobalTheory
theorem _root_.solution {τ : ClassGroup (𝓞 K) → ℍ} (hτ : ∀ c, IsIdealClassPoint σ c (τ c)) :
    (((∑ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)) / classNumber K : ℝ) : ℂ)
      = (Real.eulerMascheroniConstant + Real.log (2 * π / √d) : ℝ)
        - deriv χ.LFunction 1 / χ.LFunction 1 := by
  have h := (LFunction_one_and_mean_log_eta h2 hD hd hχ σ hτ).2
  have hd0 := discr_pos h2 hD
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have e : ∀ c, Real.log (4 * π * (τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)
      = Real.log (4 * π) + Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4) := fun c => by
    have h1 := norm_ne_zero_iff.2 (ModularForm.eta_ne_zero (τ c).2)
    have hy := (τ c).im_pos
    rw [mul_assoc, Real.log_mul (by positivity) (by positivity)]
  have e2 : Real.log (2 * π / √d) = Real.log (4 * π) - Real.log (2 * √d) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    norm_num
  simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [add_div, show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl,
    mul_div_cancel_left₀ _ hh.ne', Complex.ofReal_add, h, e2]
  push_cast
  ring
end GlobalTheory
