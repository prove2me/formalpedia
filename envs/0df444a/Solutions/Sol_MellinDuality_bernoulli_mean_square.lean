-- Prove2me | solution 1 for MellinDuality.bernoulli_mean_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:37.732567+00:00
-- url     : https://prove2.me/submissions/324569ef-5509-4fb3-a8ad-0c8765f0c643

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
public import Theorems.Thm_MellinDuality_parseval_odd
public import Theorems.Thm_MellinDuality_fam_eq_Icc
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_mellin_bernoulli
public import Theorems.Thm_MellinDuality_odd_p
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    ∑ χ ∈ oddChars p, ‖∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
        (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2)‖ ^ 2 =
      (((p : ℝ) - 1) / 2) ^ 4 := by
  set w : ℕ → ℤ := fun n => (-1 : ℤ) ^ ((n : ZMod p).val + (a * (n : ZMod p) ^ 2).val)
  have hw : ∀ n, w n * w n = 1 := fun n => by
    simp only [w]; rw [← pow_add, ← two_mul, pow_mul]; simp
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hp.out.one_lt.ne'
  have hX : ∀ χ ∈ oddChars p,
      ∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) * (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ *
          bern (χ * ψ ^ 2) =
        ((p : ℂ) - 1) / 2 * ∑ n ∈ Icc 1 ((p - 1) / 2), χ n * (w n : ℂ) := by
    intro χ hχ
    have hodd : χ (-1) = -1 := (mem_filter.1 hχ).2
    have h := mellin_bernoulli hp2 χ hodd ha
    rw [fam_eq_Icc hp2 χ a] at h
    rw [h]; field_simp
  have hN : (((p - 1) / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
    obtain ⟨k, hk⟩ := odd_p hp2
    subst hk
    rw [show (2 * k + 1 - 1) / 2 = k by omega]; push_cast; ring
  calc ∑ χ ∈ oddChars p, ‖∑ ψ ∈ oddChars p, ψ a * (1 - 2 * ψ⁻¹ 2) *
          (1 - 2 * χ 2 * ψ 2 ^ 2) * bern ψ⁻¹ * bern (χ * ψ ^ 2)‖ ^ 2
      = ∑ χ ∈ oddChars p, (((p : ℝ) - 1) / 2) ^ 2 *
          ‖∑ n ∈ Icc 1 ((p - 1) / 2), χ n * (w n : ℂ)‖ ^ 2 := by
        refine sum_congr rfl fun χ hχ => ?_
        rw [hX χ hχ, norm_mul, mul_pow]
        congr 2
        rw [norm_div, Complex.norm_ofNat]
        congr 1
        have : ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        have := hp.out.one_lt
        have : (1 : ℝ) < p := by exact_mod_cast this
        linarith
    _ = (((p : ℝ) - 1) / 2) ^ 4 := by
        rw [← mul_sum, parseval_odd w hw, hN]; ring
end MellinDuality
