-- Prove2me | solution 1 for HarrisContact.Extinction.eq_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:12:10.781255+00:00
-- url     : https://prove2.me/submissions/defe1801-774f-43b0-9719-b4cbba363695

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

open HarrisContact.Extinction in
theorem HarrisContact_eq51_transN_empty_mono {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n (ξ : Config d), Monotone (fun t : ℝ => transN μ lam n t ξ ∅) := by
  have hE : exitRate μ lam (∅ : Config d) = 0 := by simp [exitRate, bdry]
  have h0' : ∀ (ξ : Config d), Monotone (fun t : ℝ => transN μ lam 0 t ξ ∅) := by
    intro ξ t t' _
    simp only [transN]
    split_ifs with h
    · subst h; simp [hE]
    · exact le_rfl
  intro n
  induction n with
  | zero => exact h0'
  | succ n ih =>
    intro ξ t t' htt'
    simp only [transN.eq_2]
    gcongr ?_ + ?_
    · exact h0' ξ htt'
    · calc _ ≤ ∫⁻ s in Set.Icc 0 t, (ENNReal.ofReal (Real.exp (-(exitRate μ lam ξ * s))) *
              ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t' - s) ζ ∅) := by
            apply lintegral_mono; intro s
            beta_reduce
            exact mul_le_mul_right (Finset.sum_le_sum fun ζ _ =>
              mul_le_mul_right (ih ζ (by linarith)) _) _
        _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Icc_right htt')

open MeasureTheory Filter Topology ENNReal NNReal HarrisContact.Extinction in
theorem solution {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) (ξ : Config d) :
    Antitone (fun t : ℝ≥0 => surv μ lam (t : ℝ) ξ) ∧
      Tendsto (fun t : ℝ≥0 => surv μ lam (t : ℝ) ξ) atTop (𝓝 (survInf μ lam ξ)) := by
  have hmono : Monotone (fun t : ℝ => trans μ lam t ξ ∅) := fun t t' h =>
    iSup_mono (fun n => HarrisContact_eq51_transN_empty_mono μ lam n ξ h)
  have hanti : Antitone (fun t : ℝ≥0 => surv μ lam (t : ℝ) ξ) := by
    intro a b hab
    simp only [surv]
    exact tsub_le_tsub_left (hmono (by exact_mod_cast hab)) 1
  exact ⟨hanti, tendsto_atTop_iInf hanti⟩

