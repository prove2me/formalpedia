-- Prove2me | solution 1 for GlobalTheory.remainder_smooth_rough_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:30.506721+00:00
-- url     : https://prove2.me/submissions/27bd8891-d001-4c90-98ff-bd3d51d3689c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Theorems.Thm_GlobalTheory_sum_cn_isSquare_le
import Theorems.Thm_GlobalTheory_prime_power_von_mangoldt_sum_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.SizeR := by
  intro hψ
  have h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ) := fun M => by
    simpa using hψ M (Nat.cast_nonneg M)
  obtain ⟨C, hC⟩ := prime_power_von_mangoldt_sum_bound
  refine ⟨max C 10, fun ε hε _ x hx m₀ hm₀ hp => ?_⟩
  unfold Formalism.HermitianLattices.GL2a2.Rsum
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h10 : (10 : ℝ) ≤ max C 10 := le_max_right _ _
  have hw : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
  have h1 := sum_cn_isSquare_le h x (by linarith) ⌊x ^ (400 : ℝ)⌋₊
  rw [Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
  set S := m₀.primeFactors.filter (fun p => p ≤ ⌊x ^ (400 : ℝ)⌋₊) with hS
  have hsub : S ⊆ Icc 1 ⌊x ^ (ε / 5)⌋₊ := by
    intro p hpS
    simp only [hS, mem_filter, Nat.mem_primeFactors] at hpS
    obtain ⟨⟨hpp, hd, _⟩, hle⟩ := hpS
    refine mem_Icc.mpr ⟨hpp.one_le, Nat.le_floor ?_⟩
    rcases hp p hpp hd with h' | h'
    · exact h'
    · exfalso
      have : (p : ℝ) ≤ x ^ (400 : ℝ) :=
        (Nat.le_floor_iff (Real.rpow_nonneg hx0.le _)).mp hle
      linarith
  have hcard : (S.card : ℝ) ≤ x ^ (ε / 5) := by
    have := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hw)
  have h2 : ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ max C 10 * (x ^ (ε / 5) * Real.log x) := by
    calc ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ S.card • (max C 10 * Real.log x) := by
          refine sum_le_card_nsmul _ _ _ fun p hpS => ?_
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hpS).1
          exact (hC x hx p hpp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
      _ = (S.card : ℝ) * (max C 10 * Real.log x) := nsmul_eq_mul _ _
      _ ≤ x ^ (ε / 5) * (max C 10 * Real.log x) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) hlog)
      _ = max C 10 * (x ^ (ε / 5) * Real.log x) := by ring
  have h3 : 10 * x ^ ((1 : ℝ) / 2) ≤ max C 10 * x ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right h10 hs
  rw [mul_add]
  linarith
end GlobalTheory
