-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.shared_pool_bdd_to_gaussian_events
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:34:49.046183+00:00
-- url     : https://prove2.me/submissions/a91426fb-b488-4448-aa29-9b4596fee059

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_reduced_basis_admissible_width_schedule
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_finite_grid_fourier_gaussian_event_bound
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_coherent_shared_pool_fourier_sampler
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_shared_pool_decoder_coherent_copy


set_option autoImplicit false
open InfoLossLAR.WorstCase
open Filter

namespace SharedPoolCoherence
noncomputable section

def gridLoss (n : ℕ) : ℝ := 4 * Real.sqrt (2*(1/2:ℝ)^n) + (1/4:ℝ)^n

theorem gridLoss_le (n : ℕ) : gridLoss n ≤ 9 * (3/4:ℝ)^n := by
  have hroot : Real.sqrt ((1/2:ℝ)^n) ≤ (3/4:ℝ)^n := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hroot2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ) ≤ 3/4) n
  unfold gridLoss
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hmul := mul_le_mul hroot2 hroot (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤2)
  linarith

private theorem geometric_neg : Negligible (fun n => (3/4:ℝ)^n) := by
  refine ⟨fun n => by positivity, ?_⟩
  intro c hc
  obtain ⟨k,hk⟩ := exists_nat_ge c
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one k (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3/4:ℝ)<1)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨N,hN⟩ := eventually_atTop.1 ht
  refine ⟨max N 1, ?_⟩
  intro n hn
  have h1 : 1 ≤ n := (le_max_right _ _).trans hn
  have h1r : 1 ≤ (n:ℝ) := by exact_mod_cast h1
  have hm : (n:ℝ)^k * (3/4:ℝ)^n < 1 := hN n ((le_max_left _ _).trans hn)
  calc
    _ ≤ 1 / (n:ℝ)^k := (le_div_iff₀ (pow_pos (by linarith) k)).mpr (by rw [mul_comm]; exact hm.le)
    _ = (n:ℝ)^(-(k:ℝ)) := by rw [Real.rpow_neg (by positivity),Real.rpow_natCast, one_div]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1r (by linarith)

theorem residual_neg {e : ℕ → ℝ} (h : Negligible e) :
    Negligible (fun n => 2*e n + 18*(3/4:ℝ)^n) := by
  refine ⟨fun n => add_nonneg (mul_nonneg (by norm_num) (h.1 n)) (by positivity), ?_⟩
  intro c hc
  obtain ⟨N,hN⟩ := h.2 (c+1) (by positivity)
  obtain ⟨M,hM⟩ := geometric_neg.2 (c+1) (by positivity)
  refine ⟨max 20 (max N M), ?_⟩
  intro n hn
  have hn20 : 20 ≤ n := (le_max_left _ _).trans hn
  have h20 : 20 ≤ (n:ℝ) := by exact_mod_cast hn20
  have hpos : 0 < (n:ℝ) := by linarith
  have h1 := hN n ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  have h2 := hM n ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  calc
    _ ≤ 20*(n:ℝ)^(-(c+1)) := by dsimp only at *; linarith
    _ ≤ (n:ℝ)^1 * (n:ℝ)^(-(c+1)) := by
      rw [pow_one]
      exact mul_le_mul_of_nonneg_right h20 (Real.rpow_pos_of_pos hpos _).le
    _ = _ := by
      calc _ = (n:ℝ)^(1:ℝ) * (n:ℝ)^(-(c+1)) := by rw [Real.rpow_one, pow_one]
           _ = _ := by rw [← Real.rpow_add hpos]; congr 1; ring

end
end SharedPoolCoherence

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch
open scoped BigOperators Classical

theorem solution
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (C : MFamily) (hC : IsMQPT C) (P : Polynomial ℕ) (N : ℕ)
    (hbudget : CoherentPoolBDDBudget C P N S) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ → ℝ, Negligible e ∧
      ∃ N' : ℕ, ∀ n ∈ S, N' ≤ n →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∀ k : ℕ,
          let w := dgsInput B r 1 k
          outputProb H w (fun out => ∃ z : Fin n → ℤ, encVec encI z <+: out) = 1 ∧
          ∀ T : Finset (Fin n → ℤ),
            |outputProb H w (fun out => ∃ z ∈ T, encVec encI z <+: out) -
              ∑ z ∈ T, coefficientMass B r z| ≤ (e n + 1 / ((k : ℝ) + 1)) / 2 := by
  obtain ⟨H, hH, e, he, N', hrun⟩ := coherent_shared_pool_fourier_sampler S hS hpos C hC P N
    (shared_pool_decoder_coherent_copy hbudget) (fun hn B hB r hr hp => reduced_basis_admissible_width_schedule hn B hB r hr hp)
  refine ⟨H, hH, (fun n => 2*e n + 18*(3/4:ℝ)^n), SharedPoolCoherence.residual_neg he, N', ?_⟩
  intro n hn hN B hB r hr hp k
  obtain ⟨b, hb, hvalid, hread⟩ := hrun n hn hN B hB r hr hp k
  refine ⟨hvalid, ?_⟩
  intro T
  have hgrid := finite_grid_fourier_gaussian_event_bound B hB (r:ℝ) (by exact_mod_cast hr)
    (by have := hpos n hn; omega) hb T
  have hg := SharedPoolCoherence.gridLoss_le n
  change SharedPoolCoherence.gridLoss n ≤ _ at hg
  have hh := hgrid.trans hg
  let x := outputProb H (dgsInput B r 1 k) (fun out => ∃ z ∈ T, encVec encI z <+: out)
  let y := fourierEvent B (r:ℝ) (2^b) T
  let z := ∑ a ∈ T, coefficientMass B r a
  change |x-z| ≤ _
  have hxy : |x-y| ≤ e n + 1/(4*((k:ℝ)+1)) := hread T
  have hyz : |y-z| ≤ 9*(3/4:ℝ)^n := hh
  have hsplit : 1/(4*((k:ℝ)+1)) = (1/((k:ℝ)+1))/4 := by rw [← div_div]; ring
  calc
    _ ≤ |x-y| + |y-z| := abs_sub_le x y z
    _ ≤ _ := by
      rw [hsplit] at hxy
      have hpos' : 0 ≤ 1/((k:ℝ)+1) := by positivity
      dsimp only
      linarith
