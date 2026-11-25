-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_mul_pow_le_norm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:19.111113+00:00
-- url     : https://prove2.me/submissions/8d83d6b3-fc89-4268-a8b1-672cf8829497

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_totient
import Theorems.Thm_GroundTheory_PAdicHodge_zpow_p_injective
import Theorems.Thm_GroundTheory_PAdicHodge_totient_prime_pow_succ
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_pow_totient_eq_zpow
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {b : ℕ → PadicAlgCl p} (hb : ∀ i, b i ∈ cycl p k) :
    ∀ i ∈ Finset.range p, ‖b i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ i ∈ Finset.range p, b i * (ζ - 1) ^ i‖ := by
  set π := ζ - 1
  set x := ∑ i ∈ Finset.range p, b i * π ^ i
  set φ := Nat.totient (p ^ k)
  have hπpow : ‖π‖ ^ (p * φ) = (p : ℝ)⁻¹ := by
    rw [← totient_prime_pow_succ hk]; exact norm_sub_one_pow_totient hζ

  have hterm : ∀ i, b i ≠ 0 → ∃ z : ℤ, (‖b i‖ * ‖π‖ ^ i) ^ (p * φ) = (p : ℝ) ^ ((p : ℤ) * z - i) := by
    intro i hi
    obtain ⟨z, hz⟩ := exists_norm_pow_totient_eq_zpow (hb i) hi
    refine ⟨z, ?_⟩
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    calc (‖b i‖ * ‖π‖ ^ i) ^ (p * φ) = (‖b i‖ ^ φ) ^ p * (‖π‖ ^ (p * φ)) ^ i := by ring
      _ = ((p : ℝ) ^ z) ^ p * ((p : ℝ)⁻¹) ^ i := by rw [hz, hπpow]
      _ = (p : ℝ) ^ ((p : ℤ) * z - i) := by
        rw [← zpow_natCast ((p : ℝ) ^ z) p, ← zpow_mul, inv_pow, ← zpow_natCast (p : ℝ) i,
          ← zpow_neg, ← zpow_add₀ hp0]
        congr 1; ring
  have hdistinct : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range p, i ≠ j → b i ≠ 0 → b j ≠ 0 →
      ‖b i‖ * ‖π‖ ^ i ≠ ‖b j‖ * ‖π‖ ^ j := by
    intro i hi j hj hij hbi hbj h
    obtain ⟨zi, hzi⟩ := hterm i hbi
    obtain ⟨zj, hzj⟩ := hterm j hbj
    have := zpow_p_injective (p := p) (hzi.symm.trans ((congrArg (· ^ (p * φ)) h).trans hzj))
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have hdvd : (p : ℤ) ∣ ((i : ℤ) - j) := ⟨zi - zj, by linear_combination (-1 : ℤ) * this⟩
    have habs : |(i : ℤ) - j| < p := by rw [abs_lt]; constructor <;> omega
    exact hij (by have := Int.eq_zero_of_abs_lt_dvd hdvd habs; omega)
  intro i hi
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.range p) (fun i => ‖b i‖ * ‖π‖ ^ i)
    ⟨i, hi⟩
  set M := ‖b i0‖ * ‖π‖ ^ i0
  have hxM : ‖x‖ < M := lt_of_lt_of_le hlt (hmax i hi)
  have hM0 : 0 < M := lt_of_le_of_lt (norm_nonneg _) hxM
  have hbi0 : b i0 ≠ 0 := by
    intro h; rw [show M = 0 by simp [M, h]] at hM0; exact lt_irrefl 0 hM0
  have hlt' : ∀ j ∈ (Finset.range p).erase i0, ‖b j * π ^ j‖ < M := by
    intro j hj
    rw [norm_mul, norm_pow]
    rcases eq_or_ne (b j) 0 with h | h
    · rw [h, norm_zero, zero_mul]; exact hM0
    · exact lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj))
        (hdistinct j (Finset.mem_of_mem_erase hj) i0 hi0 (Finset.ne_of_mem_erase hj) h hbi0)
  set rest := ∑ j ∈ (Finset.range p).erase i0, b j * π ^ j
  have hrest : ‖rest‖ < M := by
    rcases ((Finset.range p).erase i0).eq_empty_or_nonempty with h | h
    · rw [show rest = 0 by simp [rest, h], norm_zero]; exact hM0
    · obtain ⟨j, hj, hjle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun j => b j * π ^ j)
      exact lt_of_le_of_lt hjle (hlt' j hj)
  have hx : x = b i0 * π ^ i0 + rest := (Finset.add_sum_erase _ _ hi0).symm
  have : ‖b i0 * π ^ i0‖ ≤ max ‖x‖ ‖rest‖ := by
    have h1 := IsUltrametricDist.norm_add_le_max x (-rest)
    rw [norm_neg] at h1
    calc ‖b i0 * π ^ i0‖ = ‖x + -rest‖ := by rw [hx, add_neg_cancel_right]
      _ ≤ max ‖x‖ ‖rest‖ := h1
  rw [norm_mul, norm_pow] at this
  exact absurd this (not_le.2 (max_lt hxM hrest))
end GroundTheory.PAdicHodge
