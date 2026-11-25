-- Prove2me | solution 1 for GlobalTheory.chowla_selberg_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:50.849026+00:00
-- url     : https://prove2.me/submissions/e5976eb4-c9cd-43e3-b353-8ea1b421cc45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_covolume_lattice_eq
import Theorems.Thm_GlobalTheory_chowla_selberg_lattice
import Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_eq_of_image
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
variable {𝔞 : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
  (h𝔞 : ∀ c, ClassGroup.mk K (𝔞 c) = c) {L : ClassGroup (𝓞 K) → PeriodPair}
  (hL : ∀ c, ((L c).lattice : Set ℂ) = σ '' (𝔞 c).1)
include h𝔞 hL
namespace GlobalTheory
theorem _root_.solution :
    (((∑ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖))
        / classNumber K : ℝ) : ℂ)
      = (12 * Real.log (2 * π) - 6 * Real.log d + 6 * Real.eulerMascheroniConstant : ℝ)
        - 6 * (deriv χ.LFunction 1 / χ.LFunction 1) := by
  have h0 := chowla_selberg_lattice h2 hD hd hχ σ h𝔞 hL
  have hd0 := discr_pos h2 hD
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have e : ∀ c, Real.log ((absNorm (𝔞 c).1 : ℝ) ^ 6 * ‖(L c).g₂ ^ 3 - 27 * (L c).g₃ ^ 2‖)
      = 6 * Real.log (2 * π / √d) + 6 * latticeLogPeriod (L c) := fun c => by
    obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau (L c)
    have h1 := norm_ne_zero_iff.2 (latticeCurve_Δ_ne_zero (L c))
    have h3 := norm_ne_zero_iff.2 ha
    have hy := τ.im_pos
    rw [latticeCurve_Δ] at h1
    rw [latticeLogPeriod, covolume_lattice_eq ha h, absNorm_eq_of_image h2 hD σ ha
      (τ := τ) fun z => by rw [← hL, SetLike.mem_coe, h]]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow]
    push_cast
    ring
  have e2 : Real.log (2 * π / √d) = Real.log (2 * π) - Real.log d / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hd0.le]
  simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  rw [add_div, show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl,
    mul_div_cancel_left₀ _ hh.ne', mul_div_assoc 6, Complex.ofReal_add, Complex.ofReal_mul 6 (_ / _),
    h0, e2]
  push_cast
  ring
end GlobalTheory
