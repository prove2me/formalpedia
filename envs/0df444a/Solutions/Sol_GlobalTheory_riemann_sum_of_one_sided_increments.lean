-- Prove2me | solution 1 for GlobalTheory.riemann_sum_of_one_sided_increments
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:25.159045+00:00
-- url     : https://prove2.me/submissions/a46dbd70-a5ce-4b94-8c67-a7d85977f844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannSumOfOneSidedIncrements
import Theorems.Thm_GlobalTheory_polynomial_increment_near_derivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ),
    (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) →
    Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  intro s ℓ h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous s.derivative.continuous.continuousOn) η hηpos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hnpos : (0:ℝ) < n := lt_trans (by positivity) hn
  have hn0 : n ≠ 0 := by exact_mod_cast hnpos.ne'
  have hstep : (1:ℝ) / n < δ := by
    rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hδpos] at hn; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℚ, t = fun j : ℕ => (j : ℚ) / n := ⟨_, rfl⟩
  have ht0 : ∀ j, 0 ≤ t j := fun j => by rw [ht]; positivity
  have ht1 : ∀ j ≤ n, t j ≤ 1 := fun j hj => by
    rw [ht]; show (j:ℚ) / n ≤ 1
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]; exact_mod_cast hj
  have htR : ∀ j, ((t j : ℚ) : ℝ) = (j : ℝ) / n := fun j => by rw [ht]; push_cast; ring
  have hdiff : ∀ j, ((t (j+1) : ℚ) : ℝ) - t j = 1 / n := fun j => by
    rw [htR, htR]; push_cast; ring
  have hηn : η * (1 / (n:ℝ)) = η / n := by ring
  have hup : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t j) m - ℓ (t (j+1)) m ≤
      (((t (j+1)) : ℝ) - t j) * s.derivative.eval (t j : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 j) (ht1 j hj'.le) (ht0 (j+1)) (ht1 (j+1) hj') _ (by positivity)
  have hlo : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t (j+1)) m - ℓ (t j) m ≤
      (((t j) : ℝ) - t (j+1)) * s.derivative.eval (t (j+1) : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 (j+1)) (ht1 (j+1) hj') (ht0 j) (ht1 j hj'.le) _ (by positivity)
  filter_upwards [hup, hlo] with m hu hl
  have t0 : t 0 = 0 := by rw [ht]; simp
  have tn : t n = 1 := by
    rw [ht]; show (n:ℚ) / n = 1; exact div_self (by exact_mod_cast hn0)
  have hsumℓ : ℓ 0 m - ℓ 1 m = ∑ j ∈ Finset.range n, (ℓ (t j) m - ℓ (t (j+1)) m) := by
    have := Finset.sum_range_sub' (fun j => ℓ (t j) m) n
    rw [this, t0, tn]
  have hsums : s.eval 1 - s.eval 0 =
      ∑ j ∈ Finset.range n, (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)) := by
    have := Finset.sum_range_sub (fun j => s.eval (t j : ℝ)) n
    rw [this, t0, tn]; simp
  have hstepb : ∀ j ∈ Finset.range n,
      |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| ≤ 2 * (η / n) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hd := hdiff j
    have h1n : (0:ℝ) < 1 / n := by positivity
    obtain ⟨k1, k2⟩ := polynomial_increment_near_derivative s hδ (a := t j) (b := t (j+1))
      (by exact_mod_cast ht0 j) (by linarith) (by exact_mod_cast ht1 _ hj') (by rw [hd]; exact hstep)
    have u := hu j hj
    have l := hl j hj
    have hd' : ((t j : ℚ) : ℝ) - t (j+1) = -(1 / n) := by linarith
    rw [hd] at k1 k2 u
    rw [hd'] at l
    rw [hηn] at k1 k2
    rw [abs_le]; constructor
    · nlinarith
    · nlinarith
  rw [Real.dist_eq, hsumℓ, hsums, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range n, ((ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)))|
      ≤ ∑ j ∈ Finset.range n, |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, 2 * (η / n) := Finset.sum_le_sum hstepb
    _ = 2 * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by rw [hη]; linarith
end GlobalTheory
