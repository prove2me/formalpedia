-- Prove2me | solution 1 for NonstatRL.Oracle.proposition1_oracle_gap
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:55:00.132666+00:00
-- url     : https://prove2.me/submissions/ac2a4281-c591-4b16-98df-ee44baaaf1af

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Definitions.Def_NonstatRL_Oracle_Trajectory
import Theorems.Thm_NonstatRL_Oracle_eq24_all_windows

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

theorem prop1_one_le_diameter {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S) : 1 ≤ diameter M As := by
  unfold diameter
  refine le_iSup_of_le ⟨0, hS⟩ (le_iSup_of_le ⟨0, hS⟩ (le_iInf fun f => le_iInf fun _ => ?_))
  unfold hitTime
  refine le_trans ?_ (ENNReal.le_tsum 0)
  have hset : {h : MDPTrajectory S A (0 + 1) | ∀ i : Fin (0 + 1), i ≠ 0 → (h i).1 ≠ ⟨0, hS⟩}
      = Set.univ := by
    ext h; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro i hi; exact absurd (Fin.ext (by omega)) hi
  rw [hset, measure_univ]

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (hBudget : rewardBudget M As T + 2 * Dmax * transBudget M As T ≤ (T : ℝ))
    (hPos : 0 < rewardBudget M As T + 2 * Dmax * transBudget M As T)
    (hPin : 1 ≤ (rewardBudget M As T + 2 * Dmax * transBudget M As T) * (T : ℝ))
    (s₁ : Fin S) (π : MDPPolicy S A) (hπ : IsAllowedPolicy As π) :
    expectedReward M s₁ π T -
      4 * (Dmax + 1) *
        Real.sqrt ((rewardBudget M As T + 2 * Dmax * transBudget M As T) * T) ≤
      ∑ t ∈ Finset.range T, optGain (M t) As := by
  set B := rewardBudget M As T + 2 * Dmax * transBudget M As T with hBdef
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hPos hBudget
  have hTnat : 0 < T := by exact_mod_cast hTpos
  have hD1 : 1 ≤ Dmax := by
    have h1 := le_trans (prop1_one_le_diameter (M 0) As hS) (hD 0 hTnat)
    exact (ENNReal.one_le_ofReal).mp h1
  set x := Real.sqrt (T / B) with hxdef
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = T / B := Real.sq_sqrt (div_nonneg hTpos.le hPos.le)
  have hx1 : 1 ≤ x := by
    rw [hxdef, Real.one_le_sqrt]
    rw [le_div_iff₀ hPos]; linarith
  have hxT : x ≤ T := by
    rw [hxdef, Real.sqrt_le_left hTpos.le]
    rw [div_le_iff₀ hPos]; nlinarith
  set W := ⌈x⌉₊ with hWdef
  have hWx : x ≤ (W : ℝ) := Nat.le_ceil x
  have hWx1 : (W : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hW1 : 1 ≤ W := by
    rw [hWdef, Nat.one_le_ceil_iff]; linarith
  have hWT : W ≤ T := Nat.ceil_le.mpr hxT
  have h24 := eq24_all_windows M As hS hAs T Dmax hD s₁ π hπ W hW1 hWT
  have hTB : (T : ℝ) = B * x ^ 2 := by rw [hx2]; field_simp
  have hsq : Real.sqrt (B * T) = B * x := by
    rw [show B * (T : ℝ) = (B * x) ^ 2 by rw [hTB]; ring]
    exact Real.sqrt_sq (mul_nonneg hPos.le hx0)
  rw [hsq]
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hterm1 : 4 * (T : ℝ) * Dmax / (W : ℝ) ≤ 4 * Dmax * (B * x) := by
    rw [div_le_iff₀ hWpos, hTB]
    have : 0 ≤ B * x * Dmax := by positivity
    nlinarith
  have hterm2 : 2 * (W : ℝ) * B ≤ 4 * (B * x) := by nlinarith
  linarith
