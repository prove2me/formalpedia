-- Prove2me | solution 1 for GlobalTheory.powerSum_repulsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:49.733809+00:00
-- url     : https://prove2.me/submissions/8b870b53-6a86-492f-ae69-587dc50af434

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Theorems.Thm_GlobalTheory_powerSum_weighted_ineq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι) (L δ x : ℝ), i₀ ∈ S → 1 ≤ b i₀ → 1 ≤ L → 0 < δ → 0 ≤ x → x ≤ 1 / 2 → 1 / (1 + x) ≤ ‖z i₀‖ → (∑ i ∈ S, (b i : ℝ)) ≤ L → (∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) → Real.log (1 / (C * L * δ)) / (C * L) ≤ x := by
  refine ⟨2080, by norm_num, ?_⟩
  intro ι S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp
  have h := powerSum_weighted_ineq S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp ⌈64 * L⌉₊
  set J : ℕ := ⌈64 * L⌉₊ with hJ
  have hJ1 : 64 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) ≤ 65 * L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 64 * L by linarith)
    linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hP : (1 + x) ^ J ≤ Real.exp (x * J) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) J
  have hP0 : 0 < (1 + x) ^ J := by positivity
  have h1 : (J : ℝ) * 1 ≤ J * (32 * J * δ * (1 + x) ^ J) := by nlinarith
  have h2 : 1 ≤ 32 * J * δ * (1 + x) ^ J := le_of_mul_le_mul_left h1 hJ0
  have h3 : 32 * J * δ * (1 + x) ^ J ≤ 2080 * L * δ * Real.exp (x * J) := by
    have : 32 * (J : ℝ) ≤ 2080 * L := by linarith
    gcongr
  have hD : 0 < 2080 * L * δ := by positivity
  have h4 : 1 / (2080 * L * δ) ≤ Real.exp (x * J) := by
    rw [div_le_iff₀ hD]; linarith
  have h5 : Real.log (1 / (2080 * L * δ)) ≤ x * J :=
    (Real.log_le_iff_le_exp (by positivity)).2 h4
  rw [div_le_iff₀ (by positivity)]
  have : x * J ≤ x * (2080 * L) := mul_le_mul_of_nonneg_left (by linarith) hx0
  linarith
end GlobalTheory
