-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_short_interval_large_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:09:46.260636+00:00
-- url     : https://prove2.me/submissions/e6226236-cddf-46e7-a23e-58ade5c2014b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X L : NNReal → ℝ) (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (T : NNReal) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a b : NNReal,
      a ≤ b → b ≤ T → (b:ℝ)-(a:ℝ) ≤ (T:ℝ)/(n:ℝ) →
      ρ ≤ |X b-X a| →
      ∃ s : NNReal, a < s ∧ s ≤ b ∧ ρ ≤ |X s-L s| := by
  classical
  by_contra h
  push_neg at h
  choose n hn a b hab hb hw hlarge hbad using h
  let A : ℕ → ℕ → NNReal := fun k _ => a k
  let B : ℕ → ℕ → NNReal := fun k _ => b k
  have hwidth (is ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
      Tendsto (fun k => (B (ns k) (is k):ℝ)-(A (ns k) (is k):ℝ)) atTop (nhds 0) := by
    have hn' : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
    exact squeeze_zero (fun k => sub_nonneg.mpr (by exact_mod_cast hab (ns k)))
      (fun k => hw (ns k)) ((tendsto_const_div_atTop_nhds_zero_nat (T:ℝ)).comp (hn'.comp hns))
  have hEq (s : NNReal) (hs : 0 < s) : Function.leftLim X s = L s := by
    letI : (nhdsWithin s (Iio s)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,hs⟩
    exact leftLim_eq_of_tendsto (hLeft s hs)
  have hLL (s : NNReal) (hs : s ≤ T) :
      Tendsto X (nhdsWithin s (Iio s)) (nhds (Function.leftLim X s)) := by
    by_cases h : 0 < s
    · rw [hEq s h]
      exact hLeft s h
    · have he : s = 0 := le_antisymm (le_of_not_gt h) bot_le
      subst s
      simp [Iio_bot,nhdsWithin_empty]
  obtain ⟨N,hN⟩ := AvramDividend.Classical.avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps
    X T ρ hρ A B (fun k _ => hab k) (fun k _ => hb k) hwidth hLL
    (fun s _ => (hCad s).1)
  obtain ⟨s,ha,hb,hj⟩ := hN N le_rfl 0 (hlarge N)
  rw [hEq s (bot_le.trans_lt ha)] at hj
  exact (not_lt_of_ge hj) (hbad N s ha hb)
