-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_coeff_mul_le_norm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:33.500799+00:00
-- url     : https://prove2.me/submissions/2924d369-0fc6-4e99-b606-e780216b8f3b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
import Theorems.Thm_GroundTheory_PAdicHodge_norm_le_norm_sum_of_norm_ne
import Theorems.Thm_GroundTheory_PAdicHodge_norm_zpow_mul_pow_sub_one_pow
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_eq_zpow_of_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_totient
import Theorems.Thm_GroundTheory_PAdicHodge_zpow_p_injective


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
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]
variable {k : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
include hζ
namespace GroundTheory.PAdicHodge
theorem _root_.solution (a : ℕ → ℚ_[p]) :
    ∀ i ∈ Finset.range (Nat.totient (p ^ (k + 1))),
      ‖a i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ j ∈ Finset.range (Nat.totient (p ^ (k + 1))),
        algebraMap ℚ_[p] (PadicAlgCl p) (a j) * (ζ - 1) ^ j‖ := by
  set d := Nat.totient (p ^ (k + 1))
  have hterm : ∀ i, ‖algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ i‖ = ‖a i‖ * ‖ζ - 1‖ ^ i :=
    fun i => by rw [norm_mul, norm_pow, norm_algebraMap']
  intro i hi
  rw [← hterm]
  refine norm_le_norm_sum_of_norm_ne (R := PadicAlgCl p) (Finset.range d)
    (fun j => algebraMap ℚ_[p] (PadicAlgCl p) (a j) * (ζ - 1) ^ j) (fun i hi j hj hne heq => ?_) i hi
  rw [hterm, hterm] at heq
  have hai : a i ≠ 0 := fun h => hne (by rw [h, map_zero, zero_mul])
  have hr0 : 0 < ‖ζ - 1‖ := by
    have hrd := norm_sub_one_pow_totient hζ
    by_contra h
    have h0 : ‖ζ - 1‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    have hd : d ≠ 0 := (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
    rw [h0, zero_pow hd] at hrd
    exact (inv_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℝ) ≠ 0)) hrd.symm
  have haj : a j ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at heq
    exact (mul_pos (norm_pos_iff.2 hai) (pow_pos hr0 i)).ne' heq
  obtain ⟨zi, hzi⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) hai
  obtain ⟨zj, hzj⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) haj
  rw [hzi, hzj] at heq
  have h2 := congrArg (· ^ d) heq
  rw [norm_zpow_mul_pow_sub_one_pow hζ, norm_zpow_mul_pow_sub_one_pow hζ] at h2
  have h3 := zpow_p_injective (p := p) h2
  have hdvd : (d : ℤ) ∣ ((i : ℤ) - j) := ⟨zi - zj, by linarith⟩
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  have habs : |(i : ℤ) - j| < d := by rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega
end GroundTheory.PAdicHodge
