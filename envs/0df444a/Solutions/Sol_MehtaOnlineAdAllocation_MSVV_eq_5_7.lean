-- Prove2me | solution 1 for MehtaOnlineAdAllocation.MSVV.eq_5_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:42:45.500615+00:00
-- url     : https://prove2.me/submissions/84ac0123-202f-4c25-8e8f-ab7acbd075d7

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRawRun
import Definitions.Def_AdWordsMSVV_Tradeoff_Setting

open MehtaOnlineAdAllocation.MSVV

theorem solution {N M : ℕ} (I : Instance N M)
    (hunit : ∀ u, I.budget u = 1) (k : ℕ) (hk : 1 ≤ k)
    (σ : Allocation N M) (hσ : IsRawRun I σ) (t : Fin M) (u : Fin N) :
    I.bid u t * psi ((AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) / (k : ℝ)) ≤
      gainedRawScore I σ t := by
  have hab_le : assignedBefore I σ u t.val ≤ assignedBefore I σ u M := by
    unfold assignedBefore
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨v.isLt, hv.2⟩
    · intro v _ _
      exact I.bid_nonneg u v
  have hspend_le : spend I σ u t.val ≤ spend I σ u M := by
    unfold spend
    exact min_le_min (le_refl _) hab_le
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hslab : spend I σ u M ≤ (AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_pos]
    have h1 : spend I σ u M * (k : ℝ) = (k : ℝ) * spend I σ u M := mul_comm _ _
    have h2 : (k : ℝ) * spend I σ u M ≤ (⌈(k : ℝ) * spend I σ u M⌉₊ : ℝ) :=
      Nat.le_ceil ((k : ℝ) * spend I σ u M)
    have h3 : (⌈(k : ℝ) * spend I σ u M⌉₊ : ℝ) ≤
        (AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) := by
      unfold AdWordsMSVV.Tradeoff.slabOf
      exact_mod_cast le_max_right 1 ⌈(k : ℝ) * spend I σ u M⌉₊
    linarith
  have harg : spend I σ u t.val / I.budget u ≤
      (AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) / (k : ℝ) := by
    rw [hunit u, div_one]
    exact le_trans hspend_le hslab
  have hpsi : psi ((AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) / (k : ℝ)) ≤
      psi (spend I σ u t.val / I.budget u) := by
    unfold psi
    have hexp : Real.exp (spend I σ u t.val / I.budget u - 1) ≤
        Real.exp ((AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) / (k : ℝ) - 1) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hraw : I.bid u t * psi ((AdWordsMSVV.Tradeoff.slabOf k (spend I σ u M) : ℝ) / (k : ℝ)) ≤
      rawScore I σ u t := by
    unfold rawScore
    exact mul_le_mul_of_nonneg_left hpsi (I.bid_nonneg u t)
  have hσt := hσ t
  unfold gainedRawScore
  cases h : σ t with
  | none =>
    rw [h] at hσt
    linarith [hσt u]
  | some u' =>
    rw [h] at hσt
    exact le_trans hraw (hσt.2 u)
