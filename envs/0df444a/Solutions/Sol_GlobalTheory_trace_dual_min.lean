-- Prove2me | solution 1 for GlobalTheory.trace_dual_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:51.906658+00:00
-- url     : https://prove2.me/submissions/7d3837d4-c8dc-4e94-93ad-0afe8ff1e00d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Theorems.Thm_GlobalTheory_TraceDualMin_herm_smul_left
import Theorems.Thm_GlobalTheory_TraceDualMin_herm_smul_right
import Theorems.Thm_GlobalTheory_TraceDualMin_cc_cc
import Theorems.Thm_GlobalTheory_TraceDualMin_cc_herm_self
import Theorems.Thm_GlobalTheory_TraceDualMin_trace_cc
import Theorems.Thm_GlobalTheory_TraceDualMin_isIntegral_cc
import Theorems.Thm_GlobalTheory_TraceDualMin_embedding_herm_self
import Theorems.Thm_GlobalTheory_TraceDualMin_mem_inv_different
import Theorems.Thm_GlobalTheory_absNorm_inv_differentIdeal
import Theorems.Thm_GlobalTheory_absNorm_le_abs_norm_of_mem
import Theorems.Thm_GlobalTheory_finrank_mul_abs_norm_rpow_le_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open TraceDualMin
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    (u : Fin n → E) (hu : u ≠ 0) (htr : ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (herm 1 u y) = k) :
    2 * (fdeg E : ℝ) / rdE E ^ 2 ≤ ∑ σ : E →+* ℂ, ∑ k, ‖σ (u k)‖ ^ 2 := by
  set D : FractionalIdeal (𝓞 E)⁰ E := (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot

  have h1 : ∀ y ∈ Λ, herm 1 u y ∈ D⁻¹ := by
    intro y hy
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem (⟨cc (a : E), isIntegral_cc a.isIntegral_coe⟩ : 𝓞 E) hy)
    refine ⟨k, ?_⟩
    rw [← hk]
    change _ = Algebra.trace ℚ E (herm 1 u (cc (a : E) • y))
    rw [herm_smul_right, cc_cc, mul_comm]
  have h2 : ∀ δ ∈ D, δ • u ∈ Λ := by
    intro δ hδ
    refine hdual _ fun y hy => ?_
    rw [herm_smul_left]
    have := FractionalIdeal.mul_mem_mul hδ (h1 y hy)
    rw [mul_inv_cancel₀ hD0] at this
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp this
    rw [← hb]
    exact b.isIntegral_coe
  have h3 : ∀ δ ∈ D, herm 1 u u * δ ∈ D⁻¹ := by
    intro δ hδ
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem a (h2 δ hδ))
    refine ⟨k, ?_⟩
    rw [← hk, ← trace_cc]
    change _ = Algebra.trace ℚ E (herm 1 u ((a : E) • δ • u))
    rw [herm_smul_right, herm_smul_right]
    congr 1
    conv_rhs => rw [← cc_herm_self u]
    simp only [cc, map_mul]
    ring
  have h4 : herm 1 u u ∈ D⁻¹ * D⁻¹ := by
    rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hD0]
    exact h3
  have hnorm : ∀ σ : E →+* ℂ, ‖σ (herm 1 u u)‖ = ∑ k, ‖σ (u k)‖ ^ 2 := by
    intro σ
    rw [embedding_herm_self, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h0 : herm 1 u u ≠ 0 := by
    intro h
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hnorm σ
    rw [h, map_zero, norm_zero, eq_comm,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at this
    apply hu
    funext k
    simpa using this k (Finset.mem_univ k)
  have h5 := absNorm_le_abs_norm_of_mem h4 h0
  rw [map_mul, hD, absNorm_inv_differentIdeal] at h5
  have h6 : (dE E)⁻¹ * (dE E)⁻¹ ≤ |((Algebra.norm ℚ (herm 1 u u) : ℚ) : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr h5
    simpa [dE] using h
  have h7 := finrank_mul_abs_norm_rpow_le_sum (herm 1 u u)
  simp only [hnorm] at h7
  refine le_trans ?_ h7
  have hd : 0 ≤ dE E := abs_nonneg _
  have hf : 2 * (fdeg E : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Nat.mul_div_le (Module.finrank ℚ E) 2
  have h8 : (rdE E ^ 2)⁻¹ = ((dE E)⁻¹ * (dE E)⁻¹) ^ ((Module.finrank ℚ E : ℝ)⁻¹) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hd) (inv_nonneg.mpr hd), Real.inv_rpow hd, rdE, one_div, sq,
      mul_inv]
  rw [div_eq_mul_inv, h8]
  gcongr
end GlobalTheory
