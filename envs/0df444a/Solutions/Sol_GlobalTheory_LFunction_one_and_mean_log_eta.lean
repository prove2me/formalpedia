-- Prove2me | solution 1 for GlobalTheory.LFunction_one_and_mean_log_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:39.977586+00:00
-- url     : https://prove2.me/submissions/9cf76814-6e9c-4faa-a459-89bcd9f5fa82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_QuadraticZeta_compare_expansions
import Theorems.Thm_GlobalTheory_dedekindZeta_eq_sum_realEisenstein
import Theorems.Thm_GlobalTheory_IsKroneckerChar_ne_one
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_pos
import Theorems.Thm_GlobalTheory_dedekindZeta_eq_mul_LFunction
import Theorems.Thm_GlobalTheory_tendsto_realEisenstein_sub_pole


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
namespace GlobalTheory
theorem _root_.solution [NeZero d] (h2 : finrank ℚ K = 2) (hD : discr K = -d)
    (hd : 4 < d) {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ)
    (σ : K →+* ℂ) {τ : ClassGroup (𝓞 K) → ℍ} (hτ : ∀ c, IsIdealClassPoint σ c (τ c)) :
    χ.LFunction 1 = (π * classNumber K / √d : ℝ) ∧
    (((∑ c, Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4)) / classNumber K : ℝ) : ℂ)
      = (Real.eulerMascheroniConstant - Real.log (2 * √d) : ℝ)
        - deriv χ.LFunction 1 / χ.LFunction 1 := by
  have hd0 := discr_pos h2 hD
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have hA := tendsto_finsetSum Finset.univ fun c _ => tendsto_realEisenstein_sub_pole (τ c)
  replace hA := hA.congr (f₂ := fun s : ℝ => (∑ c, ∑' p : {p : ℤ × ℤ // p ≠ 0},
      (τ c).im ^ s / ‖(p.1.1 * τ c + p.1.2 : ℂ)‖ ^ (2 * s)) - classNumber K * π / (s - 1))
    fun s => by simp [classNumber, mul_div_assoc]
  obtain ⟨e1, e2⟩ := compare_expansions
    (χ.differentiableAt_LFunction 1 (Or.inr (hχ.ne_one (by omega))))
    (show 0 < 2 / √(d : ℝ) by positivity) hA fun s hs => by
      rw [← dedekindZeta_eq_mul_LFunction h2 hD hχ (by simpa using hs),
        dedekindZeta_eq_sum_realEisenstein h2 hD hd σ hτ hs]
  have e3 : ∑ c, (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log (τ c).im
        - 2 * π * Real.log (‖ModularForm.eta (τ c)‖ ^ 2))
      = classNumber K * (2 * π * (Real.eulerMascheroniConstant - Real.log 2))
        - π * ∑ c, Real.log ((τ c).im * ‖ModularForm.eta (τ c)‖ ^ 4) := by
    rw [Finset.mul_sum, classNumber, ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Real.log_mul (τ c).im_ne_zero
      (pow_ne_zero _ (norm_ne_zero_iff.2 (ModularForm.eta_ne_zero (τ c).2))), Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  rw [e3] at e2
  refine ⟨e1.trans (congrArg _ (by ring)), ?_⟩
  rw [eq_sub_of_add_eq' e2, e1, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    ← Complex.ofReal_sub, Real.log_div two_ne_zero (by positivity),
    Real.log_mul two_ne_zero (by positivity)]
  congr 1
  field_simp
  ring
end GlobalTheory
