-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_selected_cell_near
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:49:28.793583+00:00
-- url     : https://prove2.me/submissions/d470faac-6b45-4bcb-a820-16d461a2b72f

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (T s : NNReal) (j : ℕ → ℕ)
    (hj : ∀ᶠ n : ℕ in atTop,
      j n < n ∧ T * (j n : NNReal) / (n : NNReal) < s ∧
      s ≤ T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      let a := T * (j n : NNReal) / (n : NNReal)
      let b := T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)
      a < s ∧ s ≤ b ∧ ∀ r ∈ Icc a b, dist r s < δ := by
  intro δ hδ
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
  filter_upwards [hj,hlim.eventually (gt_mem_nhds hδ)] with n hn hsm
  dsimp
  refine ⟨hn.2.1,hn.2.2,?_⟩
  intro r hr
  rw [NNReal.dist_eq,abs_lt]
  have ha : (T*(j n:NNReal)/(n:NNReal):ℝ) ≤ (r:ℝ) := by exact_mod_cast hr.1
  have hb : (r:ℝ) ≤ (T*((j n+1:ℕ):NNReal)/(n:NNReal):ℝ) := by exact_mod_cast hr.2
  have hs1 : (T*(j n:NNReal)/(n:NNReal):ℝ) ≤ (s:ℝ) := by exact_mod_cast hn.2.1.le
  have hs2 : (s:ℝ) ≤ (T*((j n+1:ℕ):NNReal)/(n:NNReal):ℝ) := by exact_mod_cast hn.2.2
  have hw : (T*((j n+1:ℕ):NNReal)/(n:NNReal):ℝ) -
      (T*(j n:NNReal)/(n:NNReal):ℝ) = (T:ℝ)/(n:ℝ) := by
    push_cast
    ring
  constructor <;> linarith
